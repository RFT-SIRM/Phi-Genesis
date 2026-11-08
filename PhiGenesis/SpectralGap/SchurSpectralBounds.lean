import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurInertiaStep

namespace PhiGenesis.SpectralGap

/-- Corner form of the response is nonnegative when both channels are nonnegative. -/
theorem sgCornerForm_nonneg (a b : ℝ) (z : TriangleCorner → ℝ)
    (hA : 0 ≤ a + 2 * b) (hE : 0 ≤ a - b) :
    0 ≤ ∑ c, z c * (a * z c + b * (∑ c', z c' - z c)) := by
  simp only [sum_triangleCorner]
  have key : ∀ z1 z2 z3 : ℝ,
      0 ≤ (a - b) * (z1 ^ 2 + z2 ^ 2 + z3 ^ 2) + b * (z1 + z2 + z3) ^ 2 := by
    intro z1 z2 z3
    nlinarith [mul_nonneg hE (sq_nonneg (z1 - z2)), mul_nonneg hE (sq_nonneg (z1 - z3)),
      mul_nonneg hE (sq_nonneg (z2 - z3)), mul_nonneg hA (sq_nonneg (z1 + z2 + z3))]
  have := key (z TriangleCorner.leftBase) (z TriangleCorner.rightBase) (z TriangleCorner.apex)
  nlinarith [this]

/-- Global nonnegativity of the shifted form from Dirichlet nonnegativity and the response. -/
theorem sgForm_nonneg_of_response (m : Nat) (lam a b : ℝ)
    (hD : SgDirichletNonneg m lam) (h : SgCornerResponse m lam a b)
    (hA : 0 ≤ a + 2 * b) (hE : 0 ≤ a - b) (y : SGVertex m → ℝ) :
    0 ≤ sgSignlessShiftedBilinearForm m lam y y := by
  obtain ⟨x, hx1, hx2, hx3⟩ := h (fun c => y (sgLevelOuterCorner m c))
  have hrz : ∀ c, (fun v => y v - x v) (sgLevelOuterCorner m c) = 0 := by
    intro c
    show y (sgLevelOuterCorner m c) - x (sgLevelOuterCorner m c) = 0
    have := hx1 c
    linarith
  have e : (fun v => x v + (y v - x v)) = y := funext fun v => by ring
  have hpol := sgSignlessShiftedBilinearForm_polarization m lam x (fun v => y v - x v)
  have hcross := sgForm_harmonic_cross m lam x (fun v => y v - x v) hx2 hrz
  have hself := sgForm_harmonic_self m lam a b x
    (fun c => y (sgLevelOuterCorner m c)) hx1 hx2 hx3
  have hnn := hD (fun v => y v - x v) hrz
  have hcf := sgCornerForm_nonneg a b (fun c => y (sgLevelOuterCorner m c)) hA hE
  rw [e] at hpol
  nlinarith [hpol, hcross, hself, hnn, hcf]

/-- A negative A1 channel gives a vector with negative energy. -/
theorem sgNegativeDirection_of_response (m : Nat) (lam a b : ℝ)
    (h : SgCornerResponse m lam a b) (hneg : a + 2 * b < 0) :
    ∃ x : SGVertex m → ℝ, sgSignlessShiftedBilinearForm m lam x x < 0 := by
  obtain ⟨x, hx1, hx2, hx3⟩ := h (fun _ => (1 : ℝ))
  refine ⟨x, ?_⟩
  have hself := sgForm_harmonic_self m lam a b x (fun _ => (1 : ℝ)) hx1 hx2 hx3
  rw [hself]
  simp only [sum_triangleCorner]
  nlinarith [hneg]

/-- Spectral bounds on every level `6 + n`: nonnegative at the lower endpoint,
a negative direction at the upper endpoint. -/
theorem sgSpectralBounds_bootstrap (n : ℕ) :
    (∀ y : SGVertex (6 + n) → ℝ,
      0 ≤ sgSignlessShiftedBilinearForm (6 + n) schurBootstrapLambdaLower y y) ∧
    (∃ x : SGVertex (6 + n) → ℝ,
      sgSignlessShiftedBilinearForm (6 + n) schurBootstrapLambdaUpper x x < 0) := by
  have hwin := schurBootstrapEndpoints_in_parameter_window
  have hLmem : schurBootstrapLambdaLower ∈
      Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper := by
    refine ⟨le_refl _, ?_⟩
    norm_num [schurBootstrapLambdaLower, schurBootstrapLambdaUpper]
  have hUmem : schurBootstrapLambdaUpper ∈
      Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper := by
    refine ⟨?_, le_refl _⟩
    norm_num [schurBootstrapLambdaLower, schurBootstrapLambdaUpper]
  have hsigns := schurBootstrapEndpoints_A1_signs_all_finite_levels
  have hrL := sgCornerResponse_trajectory_bootstrap schurBootstrapLambdaLower hLmem (6 + n)
  have hrU := sgCornerResponse_trajectory_bootstrap schurBootstrapLambdaUpper hUmem (6 + n)
  rw [schurBoundaryTrajectory_add] at hrL hrU
  have hlow := schurBootstrapLower_levelSix_certificate
  have hupp := schurBootstrapUpper_levelSix_certificate
  have hbox := schurBoundaryTrajectory_state_box schurBootstrapLambdaLower
    (schurBoundaryTrajectory schurBootstrapLambdaLower
      (2 - schurBootstrapLambdaLower, 1) 6).1
    (schurBoundaryTrajectory schurBootstrapLambdaLower
      (2 - schurBootstrapLambdaLower, 1) 6).2
    hlow.1 hlow.2.1 hlow.2.2.1 hwin.1 hwin.2.1 n
  constructor
  · intro y
    have hD := sgDirichletNonneg_bootstrap schurBootstrapLambdaLower hLmem (6 + n)
    have hA := hsigns.1 n
    have hb : (schurBoundaryTrajectory schurBootstrapLambdaLower
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (2 - schurBootstrapLambdaLower, 1) 6) n).2 ≤ 0 := hbox.2.2
    have hE : 0 ≤ (schurBoundaryTrajectory schurBootstrapLambdaLower
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (2 - schurBootstrapLambdaLower, 1) 6) n).1 -
        (schurBoundaryTrajectory schurBootstrapLambdaLower
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (2 - schurBootstrapLambdaLower, 1) 6) n).2 := by
      linarith
    exact sgForm_nonneg_of_response (6 + n) schurBootstrapLambdaLower _ _ hD hrL hA hE y
  · exact sgNegativeDirection_of_response (6 + n) schurBootstrapLambdaUpper _ _ hrU
      (hsigns.2 n)

end PhiGenesis.SpectralGap
