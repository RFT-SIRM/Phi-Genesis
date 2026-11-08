import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurInertiaBasics

namespace PhiGenesis.SpectralGap

theorem sgGlueTotal (a b lam m1 m2 m3 : ℝ) :
    ((a - b) * (0^2 + m1^2 + m2^2) + b * (0 + m1 + m2)^2) +
    ((a - b) * (m1^2 + 0^2 + m3^2) + b * (m1 + 0 + m3)^2) +
    ((a - b) * (m2^2 + m3^2 + 0^2) + b * (m2 + m3 + 0)^2) +
    lam * (m1^2 + m2^2 + m3^2) =
      (2 * a + lam - b) * (m1^2 + m2^2 + m3^2) + b * (m1 + m2 + m3)^2 := by
  ring

theorem sgGlueNonneg (c b m1 m2 m3 : ℝ) (hc : 0 ≤ c) (hc3 : 0 ≤ c + 3 * b) :
    0 ≤ c * (m1^2 + m2^2 + m3^2) + b * (m1 + m2 + m3)^2 := by
  nlinarith [sq_nonneg (m1 - m2), sq_nonneg (m1 - m3), sq_nonneg (m2 - m3),
    sq_nonneg (m1 + m2 + m3), mul_nonneg hc (sq_nonneg (m1 + m2 + m3))]

/-- Lower bound for the form by the corner form of the response. -/
theorem sgForm_ge_corner3 (m : Nat) (lam a b : ℝ)
    (hD : SgDirichletNonneg m lam) (h : SgCornerResponse m lam a b)
    (y' : SGVertex m → ℝ) (z1 z2 z3 : ℝ)
    (h1 : y' (sgLevelOuterCorner m TriangleCorner.leftBase) = z1)
    (h2 : y' (sgLevelOuterCorner m TriangleCorner.rightBase) = z2)
    (h3 : y' (sgLevelOuterCorner m TriangleCorner.apex) = z3) :
    (a - b) * (z1 ^ 2 + z2 ^ 2 + z3 ^ 2) + b * (z1 + z2 + z3) ^ 2 ≤
      sgSignlessShiftedBilinearForm m lam y' y' := by
  obtain ⟨x, hx1, hx2, hx3⟩ := h (fun c => y' (sgLevelOuterCorner m c))
  have hrz : ∀ c, (fun v => y' v - x v) (sgLevelOuterCorner m c) = 0 := by
    intro c
    show y' (sgLevelOuterCorner m c) - x (sgLevelOuterCorner m c) = 0
    have := hx1 c
    linarith
  have e : (fun v => x v + (y' v - x v)) = y' := funext fun v => by ring
  have hpol := sgSignlessShiftedBilinearForm_polarization m lam x (fun v => y' v - x v)
  have hcross := sgForm_harmonic_cross m lam x (fun v => y' v - x v) hx2 hrz
  have hself := sgForm_harmonic_self m lam a b x
    (fun c => y' (sgLevelOuterCorner m c)) hx1 hx2 hx3
  have hnn := hD (fun v => y' v - x v) hrz
  rw [e] at hpol
  simp only [sum_triangleCorner, h1, h2, h3] at hself
  nlinarith [hpol, hcross, hself, hnn]

/-- Induction step for Dirichlet nonnegativity. -/
theorem sgDirichletNonneg_succ (m : Nat) (lam a b : ℝ)
    (hD : SgDirichletNonneg m lam) (h : SgCornerResponse m lam a b)
    (hc : 0 ≤ 2 * a + lam - b) (hc3 : 0 ≤ 2 * a + lam - b + 3 * b) :
    SgDirichletNonneg (m + 1) lam := by
  intro y hy
  have hdec := sgSignlessShiftedBilinearForm_childDecomposition m lam y y
  have e0L : y (sgChildVertex m 0 (sgLevelOuterCorner m TriangleCorner.leftBase)) = 0 := by
    rw [← cr_outerP_left m]; exact hy _
  have e0R : y (sgChildVertex m 0 (sgLevelOuterCorner m TriangleCorner.rightBase)) =
      y (sgParentMidpoint01 m) := rfl
  have e0A : y (sgChildVertex m 0 (sgLevelOuterCorner m TriangleCorner.apex)) =
      y (sgParentMidpoint02 m) := rfl
  have e1L : y (sgChildVertex m 1 (sgLevelOuterCorner m TriangleCorner.leftBase)) =
      y (sgParentMidpoint01 m) := by rw [sgChildOneLeft_eq_midpoint01 m]
  have e1R : y (sgChildVertex m 1 (sgLevelOuterCorner m TriangleCorner.rightBase)) = 0 := by
    rw [← cr_outerP_right m]; exact hy _
  have e1A : y (sgChildVertex m 1 (sgLevelOuterCorner m TriangleCorner.apex)) =
      y (sgParentMidpoint12 m) := rfl
  have e2L : y (sgChildVertex m 2 (sgLevelOuterCorner m TriangleCorner.leftBase)) =
      y (sgParentMidpoint02 m) := by rw [sgChildTwoLeft_eq_midpoint02 m]
  have e2R : y (sgChildVertex m 2 (sgLevelOuterCorner m TriangleCorner.rightBase)) =
      y (sgParentMidpoint12 m) := by rw [sgChildTwoRight_eq_midpoint12 m]
  have e2A : y (sgChildVertex m 2 (sgLevelOuterCorner m TriangleCorner.apex)) = 0 := by
    rw [← cr_outerP_apex m]; exact hy _
  have h0 := sgForm_ge_corner3 m lam a b hD h (fun v => y (sgChildVertex m 0 v))
    0 (y (sgParentMidpoint01 m)) (y (sgParentMidpoint02 m)) e0L e0R e0A
  have h1 := sgForm_ge_corner3 m lam a b hD h (fun v => y (sgChildVertex m 1 v))
    (y (sgParentMidpoint01 m)) 0 (y (sgParentMidpoint12 m)) e1L e1R e1A
  have h2 := sgForm_ge_corner3 m lam a b hD h (fun v => y (sgChildVertex m 2 v))
    (y (sgParentMidpoint02 m)) (y (sgParentMidpoint12 m)) 0 e2L e2R e2A
  have hg := sgGlueTotal a b lam (y (sgParentMidpoint01 m)) (y (sgParentMidpoint02 m))
    (y (sgParentMidpoint12 m))
  have hn := sgGlueNonneg (2 * a + lam - b) b (y (sgParentMidpoint01 m))
    (y (sgParentMidpoint02 m)) (y (sgParentMidpoint12 m)) hc hc3
  nlinarith [hdec, h0, h1, h2, hg, hn]

/-- Dirichlet nonnegativity at every level for every parameter in the bootstrap window. -/
theorem sgDirichletNonneg_bootstrap (lam : ℝ)
    (hlam : lam ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) :
    ∀ N : ℕ, SgDirichletNonneg N lam := by
  intro N
  induction N with
  | zero => exact sgDirichletNonneg_zero lam
  | succ N ih =>
      have hp := schurBootstrap_all_pivots_pos lam hlam N
      have hr := sgCornerResponse_trajectory_bootstrap lam hlam N
      exact sgDirichletNonneg_succ N lam _ _ ih hr (le_of_lt hp.1) (le_of_lt hp.2)

end PhiGenesis.SpectralGap
