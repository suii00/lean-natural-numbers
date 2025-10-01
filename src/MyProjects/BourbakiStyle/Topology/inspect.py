from pathlib import Path
text = Path("TopologyB_Bourbaki2.lean").read_text(encoding="utf-8")
start = text.index("def") - 40
print(text[start:start+160].encode("unicode_escape").decode())
