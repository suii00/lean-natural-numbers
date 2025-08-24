-- Test import of PellComplete functionality
import MyProofs.Pell.Complete

-- Test basic functionality
#check PellComplete.is_pell_solution
#check PellComplete.pell_multiply
#check PellComplete.BinaryQuadraticForm
#check PellComplete.pell_2_solution

-- Test concrete theorem usage
example : PellComplete.is_pell_solution 2 3 2 := PellComplete.pell_2_solution