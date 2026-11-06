import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The three-corner Schur boundary channels

An S3-invariant boundary Schur matrix has the form (a-b) I + b J.
This file formalizes its two irreducible channels and the associated
quadratic-form decomposition. The finite-level interval/inertia checker
uses these identities after the recursive Schur elimination.
-/

namespace PhiGenesis.SpectralGap

/-- Action of the S3-invariant three-corner Schur matrix
with diagonal entry a and off-diagonal entry b on a boundary vector. -/
def schurCornerAction (a b : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (a - b) * x i + b * ∑ j : Fin 3, x j

/-- Quadratic form of the three-corner Schur boundary matrix. -/
def schurCornerEnergy (a b : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, x i * schurCornerAction a b x i

/-- The constant corner vector is the A1 channel, with eigenvalue a+2b. -/
theorem schurCornerAction_constant (a b : ℝ) (i : Fin 3) :
    schurCornerAction a b (fun _ => (1 : ℝ)) i = a + 2 * b := by
  simp [schurCornerAction]
  ring

/-- The zero-sum corner subspace is the E channel, with eigenvalue a-b. -/
theorem schurCornerAction_zeroSum (a b : ℝ) (x : Fin 3 → ℝ)
    (hsum : ∑ j : Fin 3, x j = 0) (i : Fin 3) :
    schurCornerAction a b x i = (a - b) * x i := by
  simp [schurCornerAction, hsum]

/-- The quadratic form is (a-b) sum(x_i^2) + b (sum x_i)^2. -/
theorem schurCornerEnergy_quadratic (a b : ℝ) (x : Fin 3 → ℝ) :
    schurCornerEnergy a b x =
      (a - b) * (∑ i : Fin 3, (x i) ^ 2) +
        b * (∑ i : Fin 3, x i) ^ 2 := by
  classical
  let s : ℝ := ∑ j : Fin 3, x j
  calc
    schurCornerEnergy a b x =
        ∑ i : Fin 3, ((a - b) * (x i) ^ 2 + (b * s) * x i) := by
          unfold schurCornerEnergy
          apply Finset.sum_congr rfl
          intro i hi
          simp [schurCornerAction, s]
          ring
    _ = (a - b) * (∑ i : Fin 3, (x i) ^ 2) +
          (b * s) * (∑ i : Fin 3, x i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (a - b) * (∑ i : Fin 3, (x i) ^ 2) +
          b * (∑ i : Fin 3, x i) ^ 2 := by
          dsimp [s]
          ring

/-- Subtracting the mean decomposes the squared norm into the constant
and zero-sum boundary components. -/
theorem schurCorner_centered_squares (x : Fin 3 → ℝ) :
    (∑ i : Fin 3,
      (x i - (∑ j : Fin 3, x j) / 3) ^ 2) =
      (∑ i : Fin 3, (x i) ^ 2) - ((∑ i : Fin 3, x i) ^ 2) / 3 := by
  classical
  let s : ℝ := ∑ j : Fin 3, x j
  calc
    (∑ i : Fin 3, (x i - s / 3) ^ 2) =
        ∑ i : Fin 3,
          ((x i) ^ 2 - (2 * s / 3) * x i + (s / 3) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i : Fin 3, (x i) ^ 2) -
          (2 * s / 3) * (∑ i : Fin 3, x i) +
          ∑ i : Fin 3, (s / 3) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (∑ i : Fin 3, (x i) ^ 2) -
          ((∑ i : Fin 3, x i) ^ 2) / 3 := by
          have hconst : (∑ i : Fin 3, (s / 3) ^ 2) = 3 * (s / 3) ^ 2 := by
            simp
          rw [hconst]
          dsimp [s]
          ring

/-- Orthogonal decomposition of the boundary quadratic form into its
one-dimensional A1 channel and two-dimensional E channel. -/
theorem schurCornerEnergy_decomposition (a b : ℝ) (x : Fin 3 → ℝ) :
    schurCornerEnergy a b x =
      ((a + 2 * b) / 3) * (∑ i : Fin 3, x i) ^ 2 +
        (a - b) *
          ∑ i : Fin 3, (x i - (∑ j : Fin 3, x j) / 3) ^ 2 := by
  rw [schurCornerEnergy_quadratic, schurCorner_centered_squares]
  ring

/-- If both irreducible boundary-channel eigenvalues are nonnegative,
the boundary Schur quadratic form is positive semidefinite. -/
theorem schurCornerEnergy_nonneg_of_channels (a b : ℝ) (x : Fin 3 → ℝ)
    (hA1 : 0 ≤ a + 2 * b) (hE : 0 ≤ a - b) :
    0 ≤ schurCornerEnergy a b x := by
  rw [schurCornerEnergy_decomposition]
  apply add_nonneg
  · exact mul_nonneg
      (div_nonneg hA1 (by norm_num))
      (sq_nonneg _)
  · exact mul_nonneg hE
      (Finset.sum_nonneg fun i hi => sq_nonneg _)

/-- At an A1 boundary root with b<0, the other boundary channel is
strictly positive. -/
theorem schurCorner_A1_other_channel_pos (a b : ℝ)
    (hA1 : a + 2 * b = 0) (hb : b < 0) :
    0 < a - b := by
  linarith

/-- At an A1 boundary root the three-corner Schur form is positive
semidefinite whenever b<0. -/
theorem schurCornerEnergy_nonneg_at_A1_root (a b : ℝ)
    (x : Fin 3 → ℝ) (hA1 : a + 2 * b = 0) (hb : b < 0) :
    0 ≤ schurCornerEnergy a b x := by
  have hA1_nonneg : 0 ≤ a + 2 * b := by
    rw [hA1]
  have hE_nonneg : 0 ≤ a - b :=
    le_of_lt (schurCorner_A1_other_channel_pos a b hA1 hb)
  exact schurCornerEnergy_nonneg_of_channels a b x hA1_nonneg hE_nonneg

/-- At an E boundary root with b<0, the remaining A1 channel is
strictly negative. -/
theorem schurCorner_E_other_channel_neg (a b : ℝ)
    (hE : a - b = 0) (hb : b < 0) :
    a + 2 * b < 0 := by
  linarith

/-- At an E boundary root, every zero-sum boundary vector is in the
two-dimensional kernel of the boundary Schur matrix. -/
theorem schurCornerAction_zeroSum_at_E_root (a b : ℝ)
    (x : Fin 3 → ℝ) (hE : a - b = 0)
    (hsum : ∑ j : Fin 3, x j = 0) (i : Fin 3) :
    schurCornerAction a b x i = 0 := by
  rw [schurCornerAction_zeroSum a b x hsum i]
  simp [hE]

/-- The constant boundary vector is a negative direction at an E root
when b<0. -/
theorem schurCornerEnergy_constant_neg_at_E_root (a b : ℝ)
    (hE : a - b = 0) (hb : b < 0) :
    schurCornerEnergy a b (fun _ => (1 : ℝ)) < 0 := by
  have ha : a = b := by
    linarith
  simp [schurCornerEnergy, schurCornerAction, ha]
  nlinarith


/-- The diagonal scalar of the three-midpoint pivot in one gluing step. -/
def schurMidpointPivot (a b lambda : ℝ) : ℝ :=
  2 * a + lambda - b

/-- Diagonal entry of the next three-corner Schur matrix. -/
noncomputable def schurNextDiagonal (a b c : ℝ) : ℝ :=
  a - 2 * b ^ 2 * (c + b) / (c * (c + 3 * b))

/-- Off-diagonal entry of the next three-corner Schur matrix. -/
noncomputable def schurNextOffDiagonal (b c : ℝ) : ℝ :=
  -b ^ 2 * (c - b) / (c * (c + 3 * b))

/-- At an A1 root, the next-level A1 characteristic evaluated at the
old root is exactly the displayed rational expression. -/
theorem schurNextA1_at_old_root (a b c : ℝ)
    (hA1 : a + 2 * b = 0) (hc : c ≠ 0) (hc3 : c + 3 * b ≠ 0) :
    schurNextDiagonal a b c + 2 * schurNextOffDiagonal b c =
      -2 * b * (c + 5 * b) / (c + 3 * b) := by
  unfold schurNextDiagonal schurNextOffDiagonal
  have ha : a = -2 * b := by linarith
  have hX : (c + 3 * b) * (c + 3 * b)⁻¹ = 1 := mul_inv_cancel₀ hc3
  have hY : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [ha]
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-4 * b ^ 2 * (c + 3 * b)⁻¹) * hY + (2 * b) * hX

/-- The off-diagonal Schur coefficient changes quadratically in b,
with an exact finite-level prefactor. -/
theorem schurNextOffDiagonal_div_sq (b c : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    schurNextOffDiagonal b c / b ^ 2 =
      -(c - b) / (c * (c + 3 * b)) := by
  unfold schurNextOffDiagonal
  field_simp [hb, hc]

/-- At an A1 root, the E boundary channel equals -3b. -/
theorem schurE_at_A1_root (a b : ℝ) (hA1 : a + 2 * b = 0) :
    a - b = -3 * b := by
  linarith

/-- The three-midpoint pivot is the same S3-invariant boundary form
with A1 eigenvalue c+3b and E eigenvalue c. -/
theorem schurMidpointPivot_energy_nonneg (c b : ℝ) (x : Fin 3 → ℝ)
    (hc : 0 ≤ c) (hc3 : 0 ≤ c + 3 * b) :
    0 ≤ schurCornerEnergy (c + b) b x := by
  apply schurCornerEnergy_nonneg_of_channels
  · have h : (c + b) + 2 * b = c + 3 * b := by ring
    rw [h]
    exact hc3
  · have h : (c + b) - b = c := by ring
    rw [h]
    exact hc


/-- Strict positive definiteness of the three-midpoint pivot:
positive E and A1 channel eigenvalues force strictly positive energy
on every nonzero boundary vector. -/
theorem schurMidpointPivot_energy_pos (c b : ℝ) (x : Fin 3 → ℝ)
    (hx : x ≠ 0) (hc : 0 < c) (hc3 : 0 < c + 3 * b) :
    0 < schurCornerEnergy (c + b) b x := by
  classical
  rw [schurCornerEnergy_decomposition]
  have hA1 : 0 < ((c + b) + 2 * b) / 3 := by
    have h : (c + b) + 2 * b = c + 3 * b := by ring
    rw [h]
    exact div_pos hc3 (by norm_num)
  have hE : 0 < (c + b) - b := by
    have h : (c + b) - b = c := by ring
    rw [h]
    exact hc
  have hxSome : ∃ i : Fin 3, x i ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hx
    funext i
    exact hnone i
  obtain ⟨i, hi⟩ := hxSome
  have hsq : 0 < (x i) ^ 2 := sq_pos_of_ne_zero hi
  have hsingle : (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2 :=
    Finset.single_le_sum
      (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hnorm : 0 < ∑ j : Fin 3, (x j) ^ 2 :=
    lt_of_lt_of_le hsq hsingle
  have hcenterNonneg :
      0 ≤ ∑ i : Fin 3, (x i - (∑ j : Fin 3, x j) / 3) ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hcomponents :
      0 < (∑ i : Fin 3, x i) ^ 2 +
        ∑ i : Fin 3, (x i - (∑ j : Fin 3, x j) / 3) ^ 2 := by
    rw [schurCorner_centered_squares]
    nlinarith [hnorm, sq_nonneg (∑ i : Fin 3, x i)]
  by_cases hsum : 0 < (∑ i : Fin 3, x i) ^ 2
  · exact add_pos_of_pos_of_nonneg (mul_pos hA1 hsum)
      (mul_nonneg (le_of_lt hE) hcenterNonneg)
  · have hsum0 : (∑ i : Fin 3, x i) ^ 2 = 0 := by
      exact le_antisymm (le_of_not_gt hsum) (sq_nonneg _)
    have hcenterPos :
        0 < ∑ i : Fin 3, (x i - (∑ j : Fin 3, x j) / 3) ^ 2 := by
      nlinarith [hcomponents]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt hA1) (sq_nonneg _))
      (mul_pos hE hcenterPos)

/-- The two positive midpoint-pivot eigenvalues give a positive
denominator in the scalar Schur update. -/
theorem schurMidpointPivot_denominator_pos (c b : ℝ)
    (hc : 0 < c) (hc3 : 0 < c + 3 * b) :
    0 < c * (c + 3 * b) :=
  mul_pos hc hc3

/-- Under positive midpoint pivots and c>b, the next off-diagonal
Schur coefficient is strictly negative whenever b is nonzero. -/
theorem schurNextOffDiagonal_neg (b c : ℝ)
    (hb : b ≠ 0) (hc : 0 < c) (hc3 : 0 < c + 3 * b)
    (hcb : b < c) :
    schurNextOffDiagonal b c < 0 := by
  unfold schurNextOffDiagonal
  have hnum : 0 < b ^ 2 * (c - b) :=
    mul_pos (sq_pos_of_ne_zero hb) (by linarith)
  have hden : 0 < c * (c + 3 * b) := mul_pos hc hc3
  have hratio : 0 < b ^ 2 * (c - b) / (c * (c + 3 * b)) :=
    div_pos hnum hden
  rw [show -b ^ 2 * (c - b) / (c * (c + 3 * b)) =
    -(b ^ 2 * (c - b) / (c * (c + 3 * b)) ) by ring]
  nlinarith


/-- At an A1 root, the midpoint pivot is lambda - 5*b. -/
theorem schurMidpointPivot_eq_lambda_sub_five_b_at_A1_root
    (a b lambda : ℝ) (hA1 : a + 2 * b = 0) :
    schurMidpointPivot a b lambda = lambda - 5 * b := by
  simp [schurMidpointPivot]
  linarith

/-- At an A1 root with lambda >= 1 and b < 0, the factor in the
quadratic update of the off-diagonal coefficient lies in (0, 1].
This is a pointwise estimate at the old root; it does not yet compare
coefficients evaluated at two different level roots. -/
theorem schurNextOffDiagonal_ratio_bounds_at_A1_root
    (a b lambda : ℝ) (hA1 : a + 2 * b = 0)
    (hLambda : 1 ≤ lambda) (hb : b < 0) :
    -1 ≤
        schurNextOffDiagonal b (schurMidpointPivot a b lambda) / b ^ 2 ∧
      schurNextOffDiagonal b (schurMidpointPivot a b lambda) / b ^ 2 < 0 := by
  let c : ℝ := schurMidpointPivot a b lambda
  have hc_root : c = lambda - 5 * b := by
    dsimp [c, schurMidpointPivot]
    linarith
  have hc_pos : 0 < c := by
    rw [hc_root]
    linarith
  have hc3_pos : 0 < c + 3 * b := by
    rw [hc_root]
    linarith
  have hnum_pos : 0 < c - b := by
    rw [hc_root]
    linarith
  have hden_pos : 0 < c * (c + 3 * b) :=
    mul_pos hc_pos hc3_pos
  have hnum_le_den : c - b ≤ c * (c + 3 * b) := by
    rw [hc_root]
    have hLambda_nonneg : 0 ≤ lambda := by linarith
    have hLambda_sub_one_nonneg : 0 ≤ lambda - 1 := by linarith
    have hcoeff_nonneg : 0 ≤ 7 * lambda - 6 := by linarith
    have hminus_b_nonneg : 0 ≤ -b := by linarith
    nlinarith [
      mul_nonneg hLambda_nonneg hLambda_sub_one_nonneg,
      mul_nonneg hcoeff_nonneg hminus_b_nonneg,
      sq_nonneg b
    ]
  have hfactor_pos : 0 < (c - b) / (c * (c + 3 * b)) :=
    div_pos hnum_pos hden_pos
  have hfactor_le : (c - b) / (c * (c + 3 * b)) ≤ 1 := by
    calc
      (c - b) / (c * (c + 3 * b)) ≤
          (c * (c + 3 * b)) / (c * (c + 3 * b)) :=
        div_le_div_of_nonneg_right hnum_le_den (le_of_lt hden_pos)
      _ = 1 := div_self (ne_of_gt hden_pos)
  have hb_ne : b ≠ 0 := ne_of_lt hb
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hratio := schurNextOffDiagonal_div_sq b c hb_ne hc_ne
  constructor
  · rw [hratio, neg_div]
    exact neg_le_neg hfactor_le
  · rw [hratio, neg_div]
    exact neg_neg_of_pos hfactor_pos


/-- General A1-characteristic update for one three-midpoint Schur step.
The old characteristic is a+2*b; the correction term is independent
of the diagonal parameter a. -/
theorem schurNextA1_general (a b c : ℝ)
    (hc : c ≠ 0) (hc3 : c + 3 * b ≠ 0) :
    schurNextDiagonal a b c + 2 * schurNextOffDiagonal b c =
      (a + 2 * b) - 2 * b * (c + 5 * b) / (c + 3 * b) := by
  calc
    schurNextDiagonal a b c + 2 * schurNextOffDiagonal b c =
        (a + 2 * b) +
          (schurNextDiagonal (-2 * b) b c +
            2 * schurNextOffDiagonal b c) := by
          unfold schurNextDiagonal
          ring
    _ = (a + 2 * b) - 2 * b * (c + 5 * b) / (c + 3 * b) := by
          rw [schurNextA1_at_old_root (-2 * b) b c (by ring) hc hc3]
          ring

/-- The general characteristic update written in the natural coordinates
f=a+2*b and the spectral parameter lambda. -/
theorem schurNextA1_midpoint_update (a b lambda : ℝ)
    (hc : schurMidpointPivot a b lambda ≠ 0)
    (hc3 : schurMidpointPivot a b lambda + 3 * b ≠ 0) :
    schurNextDiagonal a b (schurMidpointPivot a b lambda) +
        2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda) =
      (a + 2 * b) -
        2 * b * (lambda + 2 * (a + 2 * b)) /
          (lambda + 2 * (a + 2 * b) - 2 * b) := by
  rw [schurNextA1_general a b (schurMidpointPivot a b lambda) hc hc3]
  have hnum :
      schurMidpointPivot a b lambda + 5 * b =
        lambda + 2 * (a + 2 * b) := by
    unfold schurMidpointPivot
    ring
  have hden :
      schurMidpointPivot a b lambda + 3 * b =
        lambda + 2 * (a + 2 * b) - 2 * b := by
    unfold schurMidpointPivot
    ring
  rw [hnum, hden]

/-- At an A1 root with lambda>=1 and b<0, the next A1 boundary
characteristic is strictly positive when evaluated at the old root. -/
theorem schurNextA1_pos_at_A1_root (a b lambda : ℝ)
    (hA1 : a + 2 * b = 0) (hLambda : 1 ≤ lambda) (hb : b < 0) :
    0 <
      schurNextDiagonal a b (schurMidpointPivot a b lambda) +
        2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda) := by
  have hc_eq :
      schurMidpointPivot a b lambda = lambda - 5 * b :=
    schurMidpointPivot_eq_lambda_sub_five_b_at_A1_root a b lambda hA1
  have hc_pos : 0 < schurMidpointPivot a b lambda := by
    rw [hc_eq]
    linarith
  have hc3_eq :
      schurMidpointPivot a b lambda + 3 * b = lambda - 2 * b := by
    rw [hc_eq]
    ring
  have hc3_pos :
      0 < schurMidpointPivot a b lambda + 3 * b := by
    rw [hc3_eq]
    linarith
  rw [schurNextA1_midpoint_update a b lambda
    (ne_of_gt hc_pos) (ne_of_gt hc3_pos)]
  have hpos : 0 < (-2 * b) * lambda / (lambda - 2 * b) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hrewrite :
      (a + 2 * b) -
          2 * b * (lambda + 2 * (a + 2 * b)) /
            (lambda + 2 * (a + 2 * b) - 2 * b) =
        (-2 * b) * lambda / (lambda - 2 * b) := by
    rw [hA1]
    ring
  rw [hrewrite]
  exact hpos


/-- Exact off-diagonal update factor evaluated at an A1 root.
The expression is evaluated at the old root lambda; it is not yet
the coefficient at the next level's new root. -/
theorem schurNextOffDiagonal_ratio_at_A1_root
    (a b lambda : ℝ) (hA1 : a + 2 * b = 0)
    (hLambda : 1 ≤ lambda) (hb : b < 0) :
    schurNextOffDiagonal b (schurMidpointPivot a b lambda) / b ^ 2 =
      -(lambda - 6 * b) / ((lambda - 5 * b) * (lambda - 2 * b)) := by
  have hc_eq :
      schurMidpointPivot a b lambda = lambda - 5 * b :=
    schurMidpointPivot_eq_lambda_sub_five_b_at_A1_root a b lambda hA1
  have hc_pos : 0 < schurMidpointPivot a b lambda := by
    rw [hc_eq]
    linarith
  have hratio := schurNextOffDiagonal_div_sq b
    (schurMidpointPivot a b lambda) (ne_of_lt hb) (ne_of_gt hc_pos)
  rw [hratio, hc_eq]
  ring

/-- At an A1 root, the old-root off-diagonal update is strictly larger
than -1/lambda after division by b^2. Equivalently, its positive
magnitude is strictly below 1/lambda. -/
theorem schurNextOffDiagonal_ratio_gt_neg_inv_lambda
    (a b lambda : ℝ) (hA1 : a + 2 * b = 0)
    (hLambda : 1 ≤ lambda) (hb : b < 0) :
    -(1 / lambda) <
      schurNextOffDiagonal b (schurMidpointPivot a b lambda) / b ^ 2 := by
  have hLambda_pos : 0 < lambda := by linarith
  have hleft_pos : 0 < lambda - 5 * b := by linarith
  have hright_pos : 0 < lambda - 2 * b := by linarith
  have hden_pos :
      0 < (lambda - 5 * b) * (lambda - 2 * b) :=
    mul_pos hleft_pos hright_pos
  have hgap_pos : 0 < (-b) * (lambda - 10 * b) :=
    mul_pos (by linarith) (by linarith)
  have hcross :
      (lambda - 6 * b) * lambda <
        1 * ((lambda - 5 * b) * (lambda - 2 * b)) := by
    nlinarith [hgap_pos]
  have hfactor :
      (lambda - 6 * b) / ((lambda - 5 * b) * (lambda - 2 * b)) <
        1 / lambda :=
    (div_lt_div_iff₀ hden_pos hLambda_pos).2 hcross
  rw [schurNextOffDiagonal_ratio_at_A1_root a b lambda hA1 hLambda hb]
  rw [neg_div]
  exact neg_lt_neg hfactor



/-- A coarse local pivot box gives a strict four-fifths contraction of the
Schur off-diagonal coefficient. The all-level invariance of this box is a
separate obligation. -/
theorem schurNextOffDiagonal_abs_le_four_fifths_sq_of_box
    (b c : ℝ)
    (hb_lower : -(1 / 100 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hc_lower : (13 / 10 : ℝ) ≤ c)
    (hc_upper : c ≤ (132 / 100 : ℝ))
    (hc3_lower : (13 / 10 : ℝ) ≤ c + 3 * b) :
    |schurNextOffDiagonal b c| ≤ (4 / 5 : ℝ) * b ^ 2 := by
  have hc_pos : 0 < c := by linarith
  have hc3_pos : 0 < c + 3 * b := by linarith
  have hcb : b < c := by linarith
  have hden_pos : 0 < c * (c + 3 * b) :=
    mul_pos hc_pos hc3_pos
  have hnum_upper : c - b ≤ (133 / 100 : ℝ) := by linarith
  have hden_lower :
      (13 / 10 : ℝ) * (13 / 10 : ℝ) ≤ c * (c + 3 * b) := by
    calc
      (13 / 10 : ℝ) * (13 / 10 : ℝ) ≤ c * (13 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hc_lower (by norm_num)
      _ ≤ c * (c + 3 * b) :=
        mul_le_mul_of_nonneg_left hc3_lower (le_of_lt hc_pos)
  have hcross :
      c - b ≤ (4 / 5 : ℝ) * (c * (c + 3 * b)) := by
    calc
      c - b ≤ (133 / 100 : ℝ) := hnum_upper
      _ ≤ (4 / 5 : ℝ) * ((13 / 10 : ℝ) * (13 / 10 : ℝ)) := by norm_num
      _ ≤ (4 / 5 : ℝ) * (c * (c + 3 * b)) :=
        mul_le_mul_of_nonneg_left hden_lower (by norm_num)
  have hratio :
      (c - b) / (c * (c + 3 * b)) ≤ (4 / 5 : ℝ) :=
    (div_le_iff₀ hden_pos).2 hcross
  have hvalue_nonpos : schurNextOffDiagonal b c ≤ 0 := by
    by_cases hb : b = 0
    · simp [schurNextOffDiagonal, hb]
    · exact le_of_lt (schurNextOffDiagonal_neg b c hb hc_pos hc3_pos hcb)
  calc
    |schurNextOffDiagonal b c|
        = b ^ 2 * ((c - b) / (c * (c + 3 * b))) := by
            rw [abs_of_nonpos hvalue_nonpos]
            unfold schurNextOffDiagonal
            ring
    _ ≤ b ^ 2 * (4 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hratio (sq_nonneg b)
    _ = (4 / 5 : ℝ) * b ^ 2 := by ring


/-- The explicit tiny off-diagonal interval is invariant under one Schur
step, provided the coarse midpoint-pivot box holds. -/
theorem schurNextOffDiagonal_abs_le_six_e_minus37_of_box
    (b c : ℝ)
    (hb_lower : -(6 / 10 ^ 37 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hc_lower : (13 / 10 : ℝ) ≤ c)
    (hc_upper : c ≤ (132 / 100 : ℝ))
    (hc3_lower : (13 / 10 : ℝ) ≤ c + 3 * b) :
    |schurNextOffDiagonal b c| ≤ (6 / 10 ^ 37 : ℝ) := by
  have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b := by
    have hscale : -(1 / 100 : ℝ) ≤ -(6 / 10 ^ 37 : ℝ) := by norm_num
    exact le_trans hscale hb_lower
  have hcontract :=
    schurNextOffDiagonal_abs_le_four_fifths_sq_of_box
      b c hb_coarse_lower hb_upper hc_lower hc_upper hc3_lower
  have hBminus : 0 ≤ (6 / 10 ^ 37 : ℝ) - b := by
    linarith
  have hBplus : 0 ≤ (6 / 10 ^ 37 : ℝ) + b := by
    linarith
  have hbsq : b ^ 2 ≤ (6 / 10 ^ 37 : ℝ) ^ 2 := by
    have hprod := mul_nonneg hBminus hBplus
    nlinarith
  calc
    |schurNextOffDiagonal b c|
        ≤ (4 / 5 : ℝ) * b ^ 2 := hcontract
    _ ≤ (4 / 5 : ℝ) * (6 / 10 ^ 37 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hbsq (by norm_num)
    _ ≤ (6 / 10 ^ 37 : ℝ) := by norm_num


/-- Under the coarse midpoint-pivot box, the small off-diagonal interval is
preserved with its sign: the next coefficient remains in [-6e-37, 0]. -/
theorem schurNextOffDiagonal_signed_interval_of_box
    (b c : ℝ)
    (hb_lower : -(6 / 10 ^ 37 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hc_lower : (13 / 10 : ℝ) ≤ c)
    (hc_upper : c ≤ (132 / 100 : ℝ))
    (hc3_lower : (13 / 10 : ℝ) ≤ c + 3 * b) :
    -(6 / 10 ^ 37 : ℝ) ≤ schurNextOffDiagonal b c ∧
      schurNextOffDiagonal b c ≤ 0 := by
  have habs :=
    schurNextOffDiagonal_abs_le_six_e_minus37_of_box
      b c hb_lower hb_upper hc_lower hc_upper hc3_lower
  have hnonpos : schurNextOffDiagonal b c ≤ 0 := by
    by_cases hb : b = 0
    · simp [schurNextOffDiagonal, hb]
    · have hc_pos : 0 < c := by linarith
      have hc3_pos : 0 < c + 3 * b := by linarith
      have hcb : b < c := by linarith
      exact le_of_lt (schurNextOffDiagonal_neg b c hb hc_pos hc3_pos hcb)
  exact ⟨(abs_le.mp habs).1, hnonpos⟩

/-- The signed small off-diagonal interval is one-step invariant when the
input diagonal, off-diagonal, and spectral parameter lie in the stated
coarse state box. The parameter interval is an explicit hypothesis here. -/
theorem schurNextOffDiagonal_signed_interval_of_state_box
    (a b lambda : ℝ)
    (ha_lower : -(1 / 10 ^ 35 : ℝ) ≤ a)
    (ha_upper : a ≤ (1 / 10 ^ 35 : ℝ))
    (hb_lower : -(6 / 10 ^ 37 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    -(6 / 10 ^ 37 : ℝ) ≤
        schurNextOffDiagonal b (schurMidpointPivot a b lambda) ∧
      schurNextOffDiagonal b (schurMidpointPivot a b lambda) ≤ 0 := by
  have hc_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_upper, hlambda_lower]
  have hc_upper :
      schurMidpointPivot a b lambda ≤ (132 / 100 : ℝ) := by
    unfold schurMidpointPivot
    nlinarith [ha_upper, hb_lower, hlambda_upper]
  have hc3_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda + 3 * b := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  exact schurNextOffDiagonal_signed_interval_of_box
    b (schurMidpointPivot a b lambda)
    hb_lower hb_upper hc_lower hc_upper hc3_lower


/-- The exact change of the diagonal Schur coefficient in one step. -/
theorem schurNextDiagonal_sub_eq (a b c : ℝ) :
    schurNextDiagonal a b c - a =
      -(2 * b ^ 2 * ((c + b) / (c * (c + 3 * b)))) := by
  unfold schurNextDiagonal
  ring

/-- On the coarse positive-pivot box, the diagonal Schur coefficient moves
by at most twice the square of the old off-diagonal coefficient. -/
theorem schurNextDiagonal_change_abs_le_two_mul_sq_of_box
    (a b c : ℝ)
    (hb_lower : -(1 / 100 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hc_lower : (13 / 10 : ℝ) ≤ c)
    (hc_upper : c ≤ (132 / 100 : ℝ))
    (hc3_lower : (13 / 10 : ℝ) ≤ c + 3 * b) :
    |schurNextDiagonal a b c - a| ≤ 2 * b ^ 2 := by
  have hc_pos : 0 < c := by linarith
  have hc3_pos : 0 < c + 3 * b := by linarith
  have hden_pos : 0 < c * (c + 3 * b) :=
    mul_pos hc_pos hc3_pos
  have hnum_nonneg : 0 ≤ c + b := by linarith
  have hnum_upper : c + b ≤ (132 / 100 : ℝ) := by linarith
  have hden_lower :
      (13 / 10 : ℝ) * (13 / 10 : ℝ) ≤ c * (c + 3 * b) := by
    calc
      (13 / 10 : ℝ) * (13 / 10 : ℝ) ≤ c * (13 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hc_lower (by norm_num)
      _ ≤ c * (c + 3 * b) :=
        mul_le_mul_of_nonneg_left hc3_lower (le_of_lt hc_pos)
  have hcross : c + b ≤ c * (c + 3 * b) := by
    calc
      c + b ≤ (132 / 100 : ℝ) := hnum_upper
      _ ≤ (13 / 10 : ℝ) * (13 / 10 : ℝ) := by norm_num
      _ ≤ c * (c + 3 * b) := hden_lower
  have hratio_nonneg :
      0 ≤ (c + b) / (c * (c + 3 * b)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hratio_le :
      (c + b) / (c * (c + 3 * b)) ≤ 1 := by
    apply (div_le_iff₀ hden_pos).2
    simpa only [one_mul] using hcross
  have hcoef_nonneg : 0 ≤ 2 * b ^ 2 := by positivity
  calc
    |schurNextDiagonal a b c - a|
        = 2 * b ^ 2 * ((c + b) / (c * (c + 3 * b))) := by
          rw [schurNextDiagonal_sub_eq, abs_neg,
            abs_of_nonneg (mul_nonneg hcoef_nonneg hratio_nonneg)]
    _ ≤ 2 * b ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hratio_le hcoef_nonneg
    _ = 2 * b ^ 2 := by ring

/-- With the numerical A1 bootstrap state bounds, the diagonal Schur
increment has the explicit bound 72*10^-74. -/
theorem schurNextDiagonal_change_abs_le_72e_minus74_of_state_box
    (a b lambda : ℝ)
    (ha_lower : -(1 / 10 ^ 35 : ℝ) ≤ a)
    (ha_upper : a ≤ (1 / 10 ^ 35 : ℝ))
    (hb_lower : -(6 / 10 ^ 37 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    |schurNextDiagonal a b (schurMidpointPivot a b lambda) - a| ≤
      (72 / 10 ^ 74 : ℝ) := by
  have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b := by
    have hscale : -(1 / 100 : ℝ) ≤ -(6 / 10 ^ 37 : ℝ) := by norm_num
    exact le_trans hscale hb_lower
  have hc_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_upper, hlambda_lower]
  have hc_upper :
      schurMidpointPivot a b lambda ≤ (132 / 100 : ℝ) := by
    unfold schurMidpointPivot
    nlinarith [ha_upper, hb_lower, hlambda_upper]
  have hc3_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda + 3 * b := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  have hchange :=
    schurNextDiagonal_change_abs_le_two_mul_sq_of_box
      a b (schurMidpointPivot a b lambda)
      hb_coarse_lower hb_upper hc_lower hc_upper hc3_lower
  have hBminus : 0 ≤ (6 / 10 ^ 37 : ℝ) - b := by linarith
  have hBplus : 0 ≤ (6 / 10 ^ 37 : ℝ) + b := by linarith
  have hbsq : b ^ 2 ≤ (6 / 10 ^ 37 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hBminus hBplus]
  calc
    |schurNextDiagonal a b (schurMidpointPivot a b lambda) - a|
        ≤ 2 * b ^ 2 := hchange
    _ ≤ 2 * (6 / 10 ^ 37 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hbsq (by norm_num)
    _ = (72 / 10 ^ 74 : ℝ) := by norm_num


/-- The quadratic off-diagonal estimate and the small signed input box
give a uniform linear contraction by 10^-36. -/
theorem schurNextOffDiagonal_abs_le_e_minus36_mul_abs_of_box
    (b c : ℝ)
    (hb_lower : -(6 / 10 ^ 37 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hc_lower : (13 / 10 : ℝ) ≤ c)
    (hc_upper : c ≤ (132 / 100 : ℝ))
    (hc3_lower : (13 / 10 : ℝ) ≤ c + 3 * b) :
    |schurNextOffDiagonal b c| ≤ (1 / 10 ^ 36 : ℝ) * |b| := by
  have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b := by
    have hscale : -(1 / 100 : ℝ) ≤ -(6 / 10 ^ 37 : ℝ) := by norm_num
    exact le_trans hscale hb_lower
  have hquadratic :=
    schurNextOffDiagonal_abs_le_four_fifths_sq_of_box
      b c hb_coarse_lower hb_upper hc_lower hc_upper hc3_lower
  have hb_nonneg : 0 ≤ -b := by linarith
  have hb_small : 0 ≤ (6 / 10 ^ 37 : ℝ) + b := by linarith
  have hbsq : (-b) ^ 2 ≤ (6 / 10 ^ 37 : ℝ) * (-b) := by
    nlinarith [mul_nonneg hb_nonneg hb_small]
  have hcoeff :
      (4 / 5 : ℝ) * (6 / 10 ^ 37 : ℝ) ≤ (1 / 10 ^ 36 : ℝ) := by
    norm_num
  have hlinear :
      (4 / 5 : ℝ) * b ^ 2 ≤ (1 / 10 ^ 36 : ℝ) * (-b) := by
    calc
      (4 / 5 : ℝ) * b ^ 2 = (4 / 5 : ℝ) * (-b) ^ 2 := by ring
      _ ≤ (4 / 5 : ℝ) * ((6 / 10 ^ 37 : ℝ) * (-b)) :=
        mul_le_mul_of_nonneg_left hbsq (by norm_num)
      _ = ((4 / 5 : ℝ) * (6 / 10 ^ 37 : ℝ)) * (-b) := by ring
      _ ≤ (1 / 10 ^ 36 : ℝ) * (-b) :=
        mul_le_mul_of_nonneg_right hcoeff hb_nonneg
  calc
    |schurNextOffDiagonal b c|
        ≤ (4 / 5 : ℝ) * b ^ 2 := hquadratic
    _ ≤ (1 / 10 ^ 36 : ℝ) * (-b) := hlinear
    _ = (1 / 10 ^ 36 : ℝ) * |b| := by
      rw [abs_of_nonpos hb_upper]

/-- The same linear contraction follows from the A1 state-coordinate box
and its induced positive midpoint-pivot bounds. -/
theorem schurNextOffDiagonal_abs_le_e_minus36_mul_abs_of_state_box
    (a b lambda : ℝ)
    (ha_lower : -(1 / 10 ^ 35 : ℝ) ≤ a)
    (ha_upper : a ≤ (1 / 10 ^ 35 : ℝ))
    (hb_lower : -(6 / 10 ^ 37 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    |schurNextOffDiagonal b (schurMidpointPivot a b lambda)| ≤
      (1 / 10 ^ 36 : ℝ) * |b| := by
  have hc_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_upper, hlambda_lower]
  have hc_upper :
      schurMidpointPivot a b lambda ≤ (132 / 100 : ℝ) := by
    unfold schurMidpointPivot
    nlinarith [ha_upper, hb_lower, hlambda_upper]
  have hc3_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda + 3 * b := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  exact schurNextOffDiagonal_abs_le_e_minus36_mul_abs_of_box
    b (schurMidpointPivot a b lambda)
    hb_lower hb_upper hc_lower hc_upper hc3_lower


/-- The finite geometric sum of quarter-powers is bounded by two.
The proof keeps the positive geometric tail in the induction invariant. -/
private theorem quarter_power_sum_le_two (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k) ≤ 2 := by
  have htail : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k) +
        2 * (1 / 4 : ℝ) ^ n ≤ 2 := by
    intro n
    induction n with
    | zero =>
        norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have hpow_nonneg : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
        nlinarith
  have htailN := htail N
  have hnonneg : 0 ≤ 2 * (1 / 4 : ℝ) ^ N := by positivity
  linarith

/-- If a nonnegative sequence contracts by at least a factor 1/2 at each
step, the sum of its squares over any finite initial segment is at most
twice the square of its initial value. -/
theorem sum_sq_le_two_mul_initial_sq_of_half_contraction
    (u : ℕ → ℝ) (N : ℕ)
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hcontract : ∀ n, u (n + 1) ≤ (1 / 2 : ℝ) * u n) :
    (∑ k ∈ Finset.range N, (u k) ^ 2) ≤ 2 * (u 0) ^ 2 := by
  have hpoint : ∀ n, u n ≤ u 0 * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          u (n + 1) ≤ (1 / 2 : ℝ) * u n := hcontract n
          _ ≤ (1 / 2 : ℝ) * (u 0 * (1 / 2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = u 0 * (1 / 2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring
  have hsquare : ∀ n, (u n) ^ 2 ≤ (u 0) ^ 2 * (1 / 4 : ℝ) ^ n := by
    intro n
    have hpoint_n := hpoint n
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    have hbound_nonneg : 0 ≤ u 0 * (1 / 2 : ℝ) ^ n :=
      mul_nonneg (hu_nonneg 0) hhalf_nonneg
    have hmul_left :=
      mul_le_mul_of_nonneg_right hpoint_n (hu_nonneg n)
    have hmul_right :=
      mul_le_mul_of_nonneg_left hpoint_n hbound_nonneg
    calc
      (u n) ^ 2 = u n * u n := by ring
      _ ≤ (u 0 * (1 / 2 : ℝ) ^ n) * u n := hmul_left
      _ ≤ (u 0 * (1 / 2 : ℝ) ^ n) *
          (u 0 * (1 / 2 : ℝ) ^ n) := hmul_right
      _ = (u 0) ^ 2 * (1 / 4 : ℝ) ^ n := by
        calc
          (u 0 * (1 / 2 : ℝ) ^ n) *
              (u 0 * (1 / 2 : ℝ) ^ n)
              = (u 0) ^ 2 * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) := by ring
          _ = (u 0) ^ 2 * ((1 / 2 : ℝ) * (1 / 2 : ℝ)) ^ n := by
            rw [← mul_pow]
          _ = (u 0) ^ 2 * (1 / 4 : ℝ) ^ n := by norm_num
  calc
    (∑ k ∈ Finset.range N, (u k) ^ 2)
        ≤ ∑ k ∈ Finset.range N, (u 0) ^ 2 * (1 / 4 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          exact hsquare k
    _ = (u 0) ^ 2 *
        (∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k) := by
          rw [← Finset.mul_sum]
    _ ≤ (u 0) ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left (quarter_power_sum_le_two N) (sq_nonneg (u 0))
    _ = 2 * (u 0) ^ 2 := by ring

/-- The total finite diagonal Schur drift is at most four times the
initial off-diagonal magnitude squared, provided the latter contracts
by at least one half per step. -/
theorem diagonal_drift_total_le_four_mul_initial_sq
    (u a : ℕ → ℝ) (N : ℕ)
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hcontract : ∀ n, u (n + 1) ≤ (1 / 2 : ℝ) * u n)
    (hdiagonal_step :
      ∀ n, |a (n + 1) - a n| ≤ 2 * (u n) ^ 2) :
    |a N - a 0| ≤ 4 * (u 0) ^ 2 := by
  have hfinite : ∀ n,
      |a n - a 0| ≤
        2 * (∑ k ∈ Finset.range n, (u k) ^ 2) := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        calc
          |a (n + 1) - a 0|
              = |(a n - a 0) + (a (n + 1) - a n)| := by
                  congr 1
                  ring
          _ ≤ |a n - a 0| + |a (n + 1) - a n| :=
            abs_add _ _
          _ ≤ 2 * (∑ k ∈ Finset.range n, (u k) ^ 2) +
              2 * (u n) ^ 2 :=
            add_le_add ih (hdiagonal_step n)
          _ = 2 * ((∑ k ∈ Finset.range n, (u k) ^ 2) + (u n) ^ 2) := by
            ring
  calc
    |a N - a 0|
        ≤ 2 * (∑ k ∈ Finset.range N, (u k) ^ 2) := hfinite N
    _ ≤ 2 * (2 * (u 0) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_sq_le_two_mul_initial_sq_of_half_contraction u N hu_nonneg hcontract)
        (by norm_num)
    _ = 4 * (u 0) ^ 2 := by ring

end PhiGenesis.SpectralGap
