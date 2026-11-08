import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurCornerTrajectory

namespace PhiGenesis.SpectralGap

/-- The shifted form is the sum of `x v` times the row at `v`. -/
theorem sgShiftedForm_eq_rowSum (m : Nat) (lam : ℝ) (x : SGVertex m → ℝ) :
    sgSignlessShiftedBilinearForm m lam x x = ∑ v, x v * sgShiftedRow m lam x v := by
  unfold sgSignlessShiftedBilinearForm sgShiftedRow
  rfl

/-- Mixed form against the rows of the first argument. -/
theorem sgForm_cross_eq (m : Nat) (lam : ℝ) (x y : SGVertex m → ℝ) :
    sgSignlessShiftedBilinearForm m lam x y = ∑ u, y u * sgShiftedRow m lam x u := by
  rw [sgSignlessShiftedBilinearForm_symm]
  unfold sgSignlessShiftedBilinearForm sgShiftedRow
  rfl

/-- The three outer corners of level `m` are pairwise distinct. -/
theorem sgLevelOuterCorner_injective (m : Nat) :
    Function.Injective (sgLevelOuterCorner m) := by
  have hp : (0 : ℕ) < 2 ^ m := by positivity
  have hL : (sgLevelOuterCorner m TriangleCorner.leftBase).1 = (0, 0) :=
    sgFaceCornerCoords_all_zero_left m
  have hR : (sgLevelOuterCorner m TriangleCorner.rightBase).1 = (2 ^ m, 0) :=
    sgFaceCornerCoords_all_one_right m
  have hA : (sgLevelOuterCorner m TriangleCorner.apex).1 = (0, 2 ^ m) :=
    sgFaceCornerCoords_all_two_apex m
  intro c c' h
  have hv := congrArg Subtype.val h
  cases c <;> cases c' <;>
    first
    | rfl
    | (exfalso; simp only [hL, hR, hA, Prod.mk.injEq] at hv; omega)

/-- For harmonic `x` and `y` vanishing at the corners, the mixed form vanishes. -/
theorem sgForm_harmonic_cross (m : Nat) (lam : ℝ) (x y : SGVertex m → ℝ)
    (hx2 : ∀ v : SGVertex m, (∀ c, v ≠ sgLevelOuterCorner m c) →
      sgShiftedRow m lam x v = 0)
    (hy : ∀ c, y (sgLevelOuterCorner m c) = 0) :
    sgSignlessShiftedBilinearForm m lam x y = 0 := by
  rw [sgForm_cross_eq]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : ∃ c, u = sgLevelOuterCorner m c
  · obtain ⟨c, rfl⟩ := hu
    rw [hy c]
    simp
  · push_neg at hu
    rw [hx2 u hu]
    simp

/-- The form of a harmonic vector is the corner form of its response. -/
theorem sgForm_harmonic_self (m : Nat) (lam a b : ℝ) (x : SGVertex m → ℝ)
    (z : TriangleCorner → ℝ)
    (hx1 : ∀ c, x (sgLevelOuterCorner m c) = z c)
    (hx2 : ∀ v : SGVertex m, (∀ c, v ≠ sgLevelOuterCorner m c) →
      sgShiftedRow m lam x v = 0)
    (hx3 : ∀ c, sgShiftedRow m lam x (sgLevelOuterCorner m c) =
      a * z c + b * (∑ c', z c' - z c)) :
    sgSignlessShiftedBilinearForm m lam x x =
      ∑ c, z c * (a * z c + b * (∑ c', z c' - z c)) := by
  classical
  rw [sgShiftedForm_eq_rowSum]
  set f : SGVertex m → ℝ := fun u => x u * sgShiftedRow m lam x u with hf
  have hsub :
      ∑ u ∈ (Finset.univ : Finset TriangleCorner).image (sgLevelOuterCorner m), f u =
        ∑ u, f u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    have hno : ∀ c, u ≠ sgLevelOuterCorner m c := fun c hc =>
      hu (Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc.symm⟩)
    simp only [hf]
    rw [hx2 u hno]
    simp
  rw [← hsub, Finset.sum_image (fun c _ c' _ h => sgLevelOuterCorner_injective m h)]
  apply Finset.sum_congr rfl
  intro c _
  simp only [hf]
  rw [hx1 c, hx3 c]

/-- Dirichlet nonnegativity: the form is nonnegative on vectors vanishing at the outer corners. -/
def SgDirichletNonneg (m : Nat) (lam : ℝ) : Prop :=
  ∀ y : SGVertex m → ℝ, (∀ c, y (sgLevelOuterCorner m c) = 0) →
    0 ≤ sgSignlessShiftedBilinearForm m lam y y

private theorem outer0_eq' (f : Fin 0 → Fin 3) (c : TriangleCorner) :
    sgLevelOuterCorner 0 c = sgCornerVertex 0 (f, c) := by
  cases c
  · exact congrArg
      (fun g : Fin 0 → Fin 3 => sgCornerVertex 0 (g, TriangleCorner.leftBase))
      (Subsingleton.elim _ _)
  · exact congrArg
      (fun g : Fin 0 → Fin 3 => sgCornerVertex 0 (g, TriangleCorner.rightBase))
      (Subsingleton.elim _ _)
  · exact congrArg
      (fun g : Fin 0 → Fin 3 => sgCornerVertex 0 (g, TriangleCorner.apex))
      (Subsingleton.elim _ _)

/-- Base case: at level 0 every vertex is an outer corner. -/
theorem sgDirichletNonneg_zero (lam : ℝ) : SgDirichletNonneg 0 lam := by
  intro y hy
  have hall : ∀ v : SGVertex 0, y v = 0 := by
    intro v
    obtain ⟨⟨f, c⟩, hfc⟩ := sgCornerVertex_surjective 0 v
    rw [← hfc, ← outer0_eq' f c]
    exact hy c
  have hz : ∑ v, y v * sgShiftedRow 0 lam y v = 0 :=
    Finset.sum_eq_zero (fun u _ => by rw [hall u]; simp)
  rw [sgShiftedForm_eq_rowSum, hz]

end PhiGenesis.SpectralGap
