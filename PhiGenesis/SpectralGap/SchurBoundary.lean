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
      lambda * (lambda - 6 * b) <
        (lambda - 5 * b) * (lambda - 2 * b) := by
    nlinarith
  have hfactor :
      (lambda - 6 * b) / ((lambda - 5 * b) * (lambda - 2 * b)) <
        1 / lambda :=
    (div_lt_div_iff₀ hden_pos hLambda_pos).2 hcross
  rw [schurNextOffDiagonal_ratio_at_A1_root a b lambda hA1 hLambda hb]
  rw [neg_div]
  exact neg_lt_neg hfactor

end PhiGenesis.SpectralGap
