# ---
# jupyter:
#   jupytext:
#     text_representation:
#       extension: .py
#       format_name: percent
#   kernelspec:
#     display_name: Python 3
#     language: python
#     name: python3
# ---

# %% [markdown]
# # ポリシリアル相関のシミュレーション
# 
# このノートブックでは、ポリシリアル相関（Polyserial Correlation）の性質を
# シミュレーションを通じて確認します。

# %% [markdown]
# ## 1. 準備

# %%
import numpy as np
import matplotlib.pyplot as plt
from scipy import stats
from scipy.optimize import minimize
import warnings
warnings.filterwarnings('ignore')

# 日本語フォント設定（環境に応じて調整）
plt.rcParams['font.family'] = 'DejaVu Sans'

# %%
np.random.seed(42)

# %% [markdown]
# ## 2. データ生成関数

# %%
def generate_polyserial_data(n, rho, thresholds):
    """
    潜在変数モデルからデータを生成
    
    Parameters
    ----------
    n : int
        サンプルサイズ
    rho : float
        真の相関係数 (-1 < rho < 1)
    thresholds : array-like
        閾値パラメータ (k-1個)
    
    Returns
    -------
    X : ndarray
        連続変数 (n,)
    Y : ndarray
        順序カテゴリ変数 (n,), 値は 0, 1, ..., k-1
    Y_star : ndarray
        潜在変数 (n,)
    """
    # 二変量正規分布から (X, Y*) を生成
    mean = [0, 0]
    cov = [[1, rho], [rho, 1]]
    data = np.random.multivariate_normal(mean, cov, n)
    X = data[:, 0]
    Y_star = data[:, 1]  # 潜在変数
    
    # Y* を閾値で離散化
    Y = np.digitize(Y_star, thresholds)  # カテゴリ 0, 1, ..., k-1
    
    return X, Y, Y_star

# %% [markdown]
# ## 3. サンプルデータの生成と可視化

# %%
# パラメータ設定
n = 500              # サンプルサイズ
rho_true = 0.6       # 真の相関係数
thresholds = [-0.5, 0.8]  # 閾値 τ₁, τ₂ (3カテゴリ)

# データ生成
X, Y, Y_star = generate_polyserial_data(n, rho_true, thresholds)

print(f"カテゴリ分布: {np.bincount(Y)}")
print(f"各カテゴリの割合: {np.bincount(Y) / n}")

# %%
# 可視化
fig, axes = plt.subplots(1, 2, figsize=(12, 5))

# (a) 潜在変数モデル
ax1 = axes[0]
ax1.scatter(X, Y_star, alpha=0.5, c='steelblue')
for tau in thresholds:
    ax1.axhline(tau, color='red', linestyle='--', linewidth=2, label=f'τ = {tau}')
ax1.set_xlabel('X (Continuous)', fontsize=12)
ax1.set_ylabel('Y* (Latent)', fontsize=12)
ax1.set_title('(a) Latent Variable Model', fontsize=14)
ax1.legend()

# (b) 観測データ
ax2 = axes[1]
colors = ['#e74c3c', '#3498db', '#2ecc71']
labels = ['Low (0)', 'Medium (1)', 'High (2)']
for j in range(3):
    mask = Y == j
    ax2.scatter(X[mask], np.random.uniform(j-0.2, j+0.2, mask.sum()), 
                alpha=0.6, c=colors[j], label=labels[j], s=30)
ax2.set_xlabel('X (Continuous)', fontsize=12)
ax2.set_ylabel('Y (Observed Category)', fontsize=12)
ax2.set_yticks([0, 1, 2])
ax2.set_yticklabels(labels)
ax2.set_title('(b) Observed Data', fontsize=14)
ax2.legend()

plt.tight_layout()
plt.show()

# %% [markdown]
# ## 4. ポリシリアル相関の最尤推定

# %%
def negative_log_likelihood(params, X, Y, k):
    """
    負の対数尤度関数（最小化用）
    
    Parameters
    ----------
    params : array
        [rho, tau_1, ..., tau_{k-1}]
    X : array
        連続変数
    Y : array
        カテゴリ変数
    k : int
        カテゴリ数
    """
    rho = params[0]
    tau = params[1:]
    
    # 制約チェック
    if abs(rho) >= 0.999:
        return 1e10
    if len(tau) > 1 and not np.all(np.diff(tau) > 0):
        return 1e10
    
    sigma = np.sqrt(1 - rho**2)
    extended_tau = np.concatenate([[-1e10], tau, [1e10]])
    
    log_lik = 0
    for i in range(len(X)):
        j = Y[i]
        upper = (extended_tau[j+1] - rho * X[i]) / sigma
        lower = (extended_tau[j] - rho * X[i]) / sigma
        prob = stats.norm.cdf(upper) - stats.norm.cdf(lower)
        prob = max(prob, 1e-15)  # 数値安定性
        log_lik += np.log(prob)
    
    return -log_lik


def estimate_polyserial(X, Y):
    """ポリシリアル相関の推定"""
    k = len(np.unique(Y))
    
    # 初期値：閾値は分位点から推定
    init_tau = [stats.norm.ppf((i+1)/k) for i in range(k-1)]
    init_params = [0.0] + init_tau
    
    # 最適化
    result = minimize(
        negative_log_likelihood, 
        init_params, 
        args=(X, Y, k),
        method='Nelder-Mead',
        options={'maxiter': 1000}
    )
    
    return result.x[0], result.x[1:]  # rho_hat, tau_hat

# %%
# 推定
rho_hat, tau_hat = estimate_polyserial(X, Y)

print(f"{'='*40}")
print(f"真の相関係数 ρ:     {rho_true:.4f}")
print(f"推定値 ρ̂:          {rho_hat:.4f}")
print(f"誤差:              {rho_hat - rho_true:+.4f}")
print(f"{'='*40}")
print(f"真の閾値:          {thresholds}")
print(f"推定閾値:          {np.round(tau_hat, 4).tolist()}")

# %% [markdown]
# ## 5. ピアソン相関との比較

# %%
# 単純なピアソン相関（不適切な方法）
rho_pearson = np.corrcoef(X, Y)[0, 1]

print(f"ポリシリアル相関:  {rho_hat:.4f}")
print(f"ピアソン相関:      {rho_pearson:.4f}")
print(f"過小推定の程度:    {(rho_true - rho_pearson) / rho_true * 100:.1f}%")

# %% [markdown]
# **結論**: ピアソン相関は相関を過小評価する傾向があります。

# %% [markdown]
# ## 6. 一致性の検証

# %%
sample_sizes = [50, 100, 200, 500, 1000, 2000]
n_rep = 20  # 各サンプルサイズでの繰り返し回数

results = []
for n in sample_sizes:
    estimates = []
    for _ in range(n_rep):
        X_sim, Y_sim, _ = generate_polyserial_data(n, rho_true, thresholds)
        rho_sim, _ = estimate_polyserial(X_sim, Y_sim)
        estimates.append(rho_sim)
    
    results.append({
        'n': n,
        'mean': np.mean(estimates),
        'std': np.std(estimates),
        'bias': np.mean(estimates) - rho_true
    })
    print(f"n = {n:5d}: mean = {np.mean(estimates):.4f}, std = {np.std(estimates):.4f}")

# %%
# 一致性のプロット
fig, ax = plt.subplots(figsize=(10, 6))

ns = [r['n'] for r in results]
means = [r['mean'] for r in results]
stds = [r['std'] for r in results]

ax.errorbar(ns, means, yerr=stds, fmt='o-', capsize=5, 
            color='steelblue', markersize=8, linewidth=2)
ax.axhline(rho_true, color='red', linestyle='--', linewidth=2, label=f'True ρ = {rho_true}')
ax.set_xscale('log')
ax.set_xlabel('Sample Size (log scale)', fontsize=12)
ax.set_ylabel('Estimated ρ', fontsize=12)
ax.set_title('Consistency of Polyserial Correlation Estimator', fontsize=14)
ax.legend(fontsize=11)
ax.grid(True, alpha=0.3)
plt.tight_layout()
plt.show()

# %% [markdown]
# ## 7. k = 2 の特殊ケース（二系列相関）

# %%
# 2カテゴリの場合
thresholds_k2 = [0]  # 閾値1つのみ
X_k2, Y_k2, _ = generate_polyserial_data(500, rho_true, thresholds_k2)

rho_k2, _ = estimate_polyserial(X_k2, Y_k2)
print(f"k = 2 でのポリシリアル相関: {rho_k2:.4f}")
print("（これは二系列相関と一致する）")

# %% [markdown]
# ## 8. まとめ
# 
# 1. **ポリシリアル相関**は、連続変数と順序カテゴリ変数の間の相関を正しく推定する
# 2. **一致性**: サンプルサイズ → ∞ で真の値に収束
# 3. **ピアソン相関との違い**: ピアソン相関は相関を過小評価する
# 4. **k = 2 の場合**: 二系列相関（biserial correlation）と一致する
