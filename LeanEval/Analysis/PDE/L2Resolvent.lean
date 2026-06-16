import LeanEval.Analysis.SobolevMorrey
import EvalTools.Markers

namespace LeanEval
namespace Analysis
namespace PDE

open MeasureTheory
open scoped ENNReal

/-!
# L2 resolvent for the shifted Laplacian

For every `f ∈ L²(ℝⁿ)` and every `λ > 0`, the shifted elliptic equation
`λ v - Δ v = f` has a Sobolev solution.  The statement uses the
weak-derivative Sobolev-space definitions from `SobolevMorrey.lean`.

Since a member of `W^{1,2}` need not have a classical pointwise Laplacian,
the PDE is expressed using an `L²` weak Laplacian, and the equality with `f`
is an a.e. equality of representatives.
-/

/-- The common Euclidean domain used by the Sobolev benchmark files. -/
abbrev E (n : ℕ) := SobolevMorreyProblem.E n

/-- The multi-index corresponding to the second derivative in the `i`-th
coordinate. -/
def secondCoordinateMultiIndex {n : ℕ} (i : Fin n) : Fin n → ℕ :=
  fun j => if j = i then 2 else 0

/-- `d` is the weak second partial derivative `∂²_i v`. -/
def IsWeakSecondPartial {n : ℕ} (v d : E n → ℝ) (i : Fin n) : Prop :=
  SobolevMorreyProblem.IsWeakDeriv v d (secondCoordinateMultiIndex i)

/-- `Δv` is an `L²` weak Laplacian of `v`, represented as the sum of the weak
second coordinate derivatives. -/
def IsWeakLaplacian {n : ℕ} (v Δv : E n → ℝ) : Prop :=
  ∃ d2 : Fin n → E n → ℝ,
    (∀ i, IsWeakSecondPartial v (d2 i) i ∧ MemLp (d2 i) (2 : ℝ≥0∞) volume) ∧
      Δv =ᵐ[volume] fun x => ∑ i, d2 i x

/-- **L2 resolvent for the shifted Laplacian.** For every
`f ∈ L²(ℝⁿ)` and every `λ > 0`, there exists
`v ∈ W^{1,2}(ℝⁿ)` with an `L²` weak Laplacian such that
`λ v - Δ v = f` a.e. -/
@[eval_problem]
theorem elliptic_l2_resolvent {n : ℕ} {lambda : ℝ} (_hlambda : 0 < lambda)
    (f : E n → ℝ) (_hf : MemLp f (2 : ℝ≥0∞) volume) :
    ∃ v : E n → ℝ,
      SobolevMorreyProblem.MemSobolevWk 1 (2 : ℝ≥0∞) v ∧
        ∃ Δv : E n → ℝ,
          IsWeakLaplacian v Δv ∧ MemLp Δv (2 : ℝ≥0∞) volume ∧
            (fun x => lambda * v x - Δv x) =ᵐ[volume] f := by
  sorry

end PDE
end Analysis
end LeanEval
