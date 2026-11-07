import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences

open Filter
open scoped Topology

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


/-- The wider level-three off-diagonal interval is preserved by one
Schur step under the same coarse positive-pivot hypotheses. -/
theorem schurNextOffDiagonal_signed_interval_of_coarse_box
    (b c : ℝ)
    (hb_lower : -(1 / 20000 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hc_lower : (13 / 10 : ℝ) ≤ c)
    (hc_upper : c ≤ (132 / 100 : ℝ))
    (hc3_lower : (13 / 10 : ℝ) ≤ c + 3 * b) :
    -(1 / 20000 : ℝ) ≤ schurNextOffDiagonal b c ∧
      schurNextOffDiagonal b c ≤ 0 := by
  have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b := by
    have hscale : -(1 / 100 : ℝ) ≤ -(1 / 20000 : ℝ) := by
      norm_num
    exact le_trans hscale hb_lower
  have hcontract :=
    schurNextOffDiagonal_abs_le_four_fifths_sq_of_box
      b c hb_coarse_lower hb_upper hc_lower hc_upper hc3_lower
  have hb_nonneg : 0 ≤ -b := by linarith
  have hb_mag_upper : -b ≤ (1 / 20000 : ℝ) := by linarith
  have hbsq : b ^ 2 ≤ (1 / 20000 : ℝ) * (-b) := by
    calc
      b ^ 2 = (-b) * (-b) := by ring
      _ ≤ (1 / 20000 : ℝ) * (-b) :=
        mul_le_mul_of_nonneg_right hb_mag_upper hb_nonneg
  have habs :
      |schurNextOffDiagonal b c| ≤ (1 / 20000 : ℝ) := by
    calc
      |schurNextOffDiagonal b c|
          ≤ (4 / 5 : ℝ) * b ^ 2 := hcontract
      _ ≤ (4 / 5 : ℝ) *
          ((1 / 20000 : ℝ) * (-b)) :=
        mul_le_mul_of_nonneg_left hbsq (by norm_num)
      _ ≤ (4 / 5 : ℝ) *
          ((1 / 20000 : ℝ) * (1 / 20000 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hb_mag_upper (by norm_num))
          (by norm_num)
      _ ≤ (1 / 20000 : ℝ) := by norm_num
  have hnonpos : schurNextOffDiagonal b c ≤ 0 := by
    by_cases hb : b = 0
    · simp [schurNextOffDiagonal, hb]
    · have hc_pos : 0 < c := by linarith
      have hc3_pos : 0 < c + 3 * b := by linarith
      have hcb : b < c := by linarith
      exact le_of_lt
        (schurNextOffDiagonal_neg b c hb hc_pos hc3_pos hcb)
  exact ⟨(abs_le.mp habs).1, hnonpos⟩


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
  have habs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
    apply abs_le.mpr
    constructor
    · calc
        -(|x| + |y|) = (-|x|) + (-|y|) := by ring
        _ ≤ x + y := add_le_add (neg_abs_le x) (neg_abs_le y)
    · exact add_le_add (le_abs_self x) (le_abs_self y)
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
            habs_add _ _
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


/-- Finite-horizon diagonal drift bound. Only the hypotheses on indices
strictly before N are needed; after N, extend u by zero and hold a fixed. -/
theorem diagonal_drift_total_le_four_mul_initial_sq_until
    (u a : ℕ → ℝ) (N : ℕ)
    (hu_nonneg : ∀ n, n ≤ N → 0 ≤ u n)
    (hcontract : ∀ n, n < N →
      u (n + 1) ≤ (1 / 2 : ℝ) * u n)
    (hdiagonal_step :
      ∀ n, n < N → |a (n + 1) - a n| ≤ 2 * (u n) ^ 2) :
    |a N - a 0| ≤ 4 * (u 0) ^ 2 := by
  let uExt : ℕ → ℝ := fun n => if n ≤ N then u n else 0
  let aExt : ℕ → ℝ := fun n => if n ≤ N then a n else a N
  have huExt_nonneg : ∀ n, 0 ≤ uExt n := by
    intro n
    by_cases hn : n ≤ N
    · simpa [uExt, hn] using hu_nonneg n hn
    · simp [uExt, hn]
  have hcontractExt : ∀ n,
      uExt (n + 1) ≤ (1 / 2 : ℝ) * uExt n := by
    intro n
    by_cases hn : n ≤ N
    · by_cases hn1 : n + 1 ≤ N
      · have hlt : n < N := by omega
        simpa [uExt, hn, hn1] using hcontract n hlt
      · have heq : n = N := by omega
        subst n
        have hnonneg : 0 ≤ u N := hu_nonneg N le_rfl
        have hnext : ¬ N + 1 ≤ N := by omega
        simp [uExt, hnext]
        positivity
    · have hn1 : ¬ n + 1 ≤ N := by omega
      simp [uExt, hn, hn1]
  have hdiagonalExt : ∀ n,
      |aExt (n + 1) - aExt n| ≤ 2 * (uExt n) ^ 2 := by
    intro n
    by_cases hn : n ≤ N
    · by_cases hn1 : n + 1 ≤ N
      · have hlt : n < N := by omega
        simpa [aExt, uExt, hn, hn1] using hdiagonal_step n hlt
      · have heq : n = N := by omega
        subst n
        have hnext : ¬ N + 1 ≤ N := by omega
        simp [aExt, uExt, hnext]
        positivity
    · have hn1 : ¬ n + 1 ≤ N := by omega
      simp [aExt, uExt, hn, hn1]
  have htotal :=
    diagonal_drift_total_le_four_mul_initial_sq
      uExt aExt N huExt_nonneg hcontractExt hdiagonalExt
  simpa [uExt, aExt] using htotal

/-- With the level-6 off-diagonal bound, the finite total diagonal drift
is at most 1.44e-72. The hypotheses are only required through N. -/
theorem diagonal_drift_total_le_144_e_minus72_until
    (u a : ℕ → ℝ) (N : ℕ)
    (hu_nonneg : ∀ n, n ≤ N → 0 ≤ u n)
    (hcontract : ∀ n, n < N →
      u (n + 1) ≤ (1 / 2 : ℝ) * u n)
    (hdiagonal_step :
      ∀ n, n < N → |a (n + 1) - a n| ≤ 2 * (u n) ^ 2)
    (hu0_upper : u 0 ≤ (6 / 10 ^ 37 : ℝ)) :
    |a N - a 0| ≤ (144 / 10 ^ 74 : ℝ) := by
  have htotal :=
    diagonal_drift_total_le_four_mul_initial_sq_until
      u a N hu_nonneg hcontract hdiagonal_step
  have hu0_nonneg : 0 ≤ u 0 := hu_nonneg 0 (Nat.zero_le N)
  have hsq :
      (u 0) ^ 2 ≤ (6 / 10 ^ 37 : ℝ) ^ 2 := by
    nlinarith
  calc
    |a N - a 0| ≤ 4 * (u 0) ^ 2 := htotal
    _ ≤ 4 * (6 / 10 ^ 37 : ℝ) ^ 2 := by nlinarith
    _ = (144 / 10 ^ 74 : ℝ) := by norm_num


/-- A small initial diagonal value remains inside the coarse diagonal box
whenever the accumulated Schur drift is bounded by 1.44e-72. -/
theorem schurDiagonal_abs_le_e_minus35_of_initial_three_e_minus36_and_drift
    (a a₀ : ℝ)
    (ha₀ : |a₀| ≤ (3 / 10 ^ 36 : ℝ))
    (hdrift : |a - a₀| ≤ (144 / 10 ^ 74 : ℝ)) :
    |a| ≤ (1 / 10 ^ 35 : ℝ) := by
  have habs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
    apply abs_le.mpr
    constructor
    · calc
        -(|x| + |y|) = (-|x|) + (-|y|) := by ring
        _ ≤ x + y := add_le_add (neg_abs_le x) (neg_abs_le y)
    · exact add_le_add (le_abs_self x) (le_abs_self y)
  calc
    |a| = |(a - a₀) + a₀| := by congr 1; ring
    _ ≤ |a - a₀| + |a₀| := habs_add _ _
    _ ≤ (144 / 10 ^ 74 : ℝ) + (3 / 10 ^ 36 : ℝ) :=
      add_le_add hdrift ha₀
    _ ≤ (1 / 10 ^ 35 : ℝ) := by norm_num


/-- One exact three-corner Schur update on the scalar boundary state. -/
noncomputable def schurBoundaryStateStep (lambda : ℝ) (state : ℝ × ℝ) :
    ℝ × ℝ :=
  (schurNextDiagonal state.1 state.2
      (schurMidpointPivot state.1 state.2 lambda),
   schurNextOffDiagonal state.2
      (schurMidpointPivot state.1 state.2 lambda))

/-- The scalar Schur trajectory starting from an arbitrary boundary state
at a fixed spectral parameter. -/
noncomputable def schurBoundaryTrajectory (lambda : ℝ) (initial : ℝ × ℝ) :
    ℕ → ℝ × ℝ
  | 0 => initial
  | n + 1 => schurBoundaryStateStep lambda
      (schurBoundaryTrajectory lambda initial n)

/-- For a fixed lambda in [1.309,1.31], the full diagonal/off-diagonal
state box is invariant along the exact Schur recurrence, provided the
level-six starting state lies in the sharper interval
|a_0| <= 3e-36 and b_0 in [-6e-37,0]. -/
theorem schurStateBox_invariant_of_recursion
    (a b : ℕ → ℝ) (lambda : ℝ)
    (ha0 : |a 0| ≤ (3 / 10 ^ 36 : ℝ))
    (hb0_lower : -(6 / 10 ^ 37 : ℝ) ≤ b 0)
    (hb0_upper : b 0 ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ))
    (ha_step : ∀ n,
      a (n + 1) =
        schurNextDiagonal (a n) (b n)
          (schurMidpointPivot (a n) (b n) lambda))
    (hb_step : ∀ n,
      b (n + 1) =
        schurNextOffDiagonal (b n)
          (schurMidpointPivot (a n) (b n) lambda)) :
    ∀ n, |a n| ≤ (1 / 10 ^ 35 : ℝ) ∧
      -(6 / 10 ^ 37 : ℝ) ≤ b n ∧ b n ≤ 0 := by
  have hb0_abs : |b 0| ≤ (6 / 10 ^ 37 : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact hb0_lower
    · exact le_trans hb0_upper (by norm_num)
  have hsq_abs (x : ℝ) : (|x|) ^ 2 = x ^ 2 := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      ring
  have hprefix : ∀ n, ∀ k ≤ n,
      |a k| ≤ (1 / 10 ^ 35 : ℝ) ∧
        -(6 / 10 ^ 37 : ℝ) ≤ b k ∧ b k ≤ 0 := by
    intro n
    induction n with
    | zero =>
        intro k hk
        have hk0 : k = 0 := by omega
        subst k
        have ha0_box : |a 0| ≤ (1 / 10 ^ 35 : ℝ) := by
          exact le_trans ha0 (by norm_num)
        exact ⟨ha0_box, hb0_lower, hb0_upper⟩
    | succ n ih =>
        intro k hk
        by_cases hk_old : k ≤ n
        · exact ih k hk_old
        · have hk_eq : k = n + 1 := by omega
          subst k
          have hstate_n : |a n| ≤ (1 / 10 ^ 35 : ℝ) ∧
              -(6 / 10 ^ 37 : ℝ) ≤ b n ∧ b n ≤ 0 := ih n le_rfl
          have hu_nonneg : ∀ j, j ≤ n + 1 → 0 ≤ |b j| := by
            intro j hj
            exact abs_nonneg (b j)
          have hcontract_prefix : ∀ j, j < n + 1 →
              |b (j + 1)| ≤ (1 / 2 : ℝ) * |b j| := by
            intro j hj
            have hj_le : j ≤ n := by omega
            have hstate_j := ih j hj_le
            have ha_j_bounds := abs_le.mp hstate_j.1
            have hlinear :=
              schurNextOffDiagonal_abs_le_e_minus36_mul_abs_of_state_box
                (a j) (b j) lambda
                ha_j_bounds.1 ha_j_bounds.2
                hstate_j.2.1 hstate_j.2.2
                hlambda_lower hlambda_upper
            calc
              |b (j + 1)| =
                  |schurNextOffDiagonal (b j)
                    (schurMidpointPivot (a j) (b j) lambda)| := by
                      rw [hb_step j]
              _ ≤ (1 / 10 ^ 36 : ℝ) * |b j| := hlinear
              _ ≤ (1 / 2 : ℝ) * |b j| :=
                mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
          have hdiagonal_prefix : ∀ j, j < n + 1 →
              |a (j + 1) - a j| ≤ 2 * (|b j|) ^ 2 := by
            intro j hj
            have hj_le : j ≤ n := by omega
            have hstate_j := ih j hj_le
            have ha_j_bounds := abs_le.mp hstate_j.1
            have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b j := by
              have hscale : -(1 / 100 : ℝ) ≤ -(6 / 10 ^ 37 : ℝ) := by
                norm_num
              exact le_trans hscale hstate_j.2.1
            have hc_lower :
                (13 / 10 : ℝ) ≤ schurMidpointPivot (a j) (b j) lambda := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.1, hstate_j.2.2, hlambda_lower]
            have hc_upper :
                schurMidpointPivot (a j) (b j) lambda ≤ (132 / 100 : ℝ) := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.2, hstate_j.2.1, hlambda_upper]
            have hc3_lower :
                (13 / 10 : ℝ) ≤
                  schurMidpointPivot (a j) (b j) lambda + 3 * b j := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.1, hstate_j.2.1, hlambda_lower]
            have hlocal :=
              schurNextDiagonal_change_abs_le_two_mul_sq_of_box
                (a j) (b j) (schurMidpointPivot (a j) (b j) lambda)
                hb_coarse_lower hstate_j.2.2
                hc_lower hc_upper hc3_lower
            calc
              |a (j + 1) - a j| =
                  |schurNextDiagonal (a j) (b j)
                    (schurMidpointPivot (a j) (b j) lambda) - a j| := by
                      rw [ha_step j]
              _ ≤ 2 * (b j) ^ 2 := hlocal
              _ = 2 * (|b j|) ^ 2 := by rw [← hsq_abs (b j)]
          have hdrift :=
            diagonal_drift_total_le_144_e_minus72_until
              (fun j => |b j|) a (n + 1)
              hu_nonneg hcontract_prefix hdiagonal_prefix hb0_abs
          have ha_new :=
            schurDiagonal_abs_le_e_minus35_of_initial_three_e_minus36_and_drift
              (a (n + 1)) (a 0) ha0 hdrift
          have ha_n_bounds := abs_le.mp hstate_n.1
          have hb_new :=
            schurNextOffDiagonal_signed_interval_of_state_box
              (a n) (b n) lambda
              ha_n_bounds.1 ha_n_bounds.2
              hstate_n.2.1 hstate_n.2.2
              hlambda_lower hlambda_upper
          rw [← hb_step n] at hb_new
          exact ⟨ha_new, hb_new.1, hb_new.2⟩
  intro n
  exact hprefix n n le_rfl

/-- The concrete trajectory constructor satisfies the full conditional
state-box induction above. -/
theorem schurBoundaryTrajectory_state_box
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (3 / 10 ^ 36 : ℝ))
    (hb₀_lower : -(6 / 10 ^ 37 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    ∀ n, |(schurBoundaryTrajectory lambda (a₀, b₀) n).1| ≤
        (1 / 10 ^ 35 : ℝ) ∧
      -(6 / 10 ^ 37 : ℝ) ≤
        (schurBoundaryTrajectory lambda (a₀, b₀) n).2 ∧
      (schurBoundaryTrajectory lambda (a₀, b₀) n).2 ≤ 0 := by
  let a : ℕ → ℝ := fun n =>
    (schurBoundaryTrajectory lambda (a₀, b₀) n).1
  let b : ℕ → ℝ := fun n =>
    (schurBoundaryTrajectory lambda (a₀, b₀) n).2
  have ha_step : ∀ n,
      a (n + 1) =
        schurNextDiagonal (a n) (b n)
          (schurMidpointPivot (a n) (b n) lambda) := by
    intro n
    rfl
  have hb_step : ∀ n,
      b (n + 1) =
        schurNextOffDiagonal (b n)
          (schurMidpointPivot (a n) (b n) lambda) := by
    intro n
    rfl
  have hstate :=
    schurStateBox_invariant_of_recursion
      a b lambda ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper ha_step hb_step
  intro n
  simpa [a, b] using hstate n


/-- A coarser Schur state box is invariant at every finite horizon
when the initial diagonal coefficient is at most 1/500 and the initial
off-diagonal coefficient lies in [-1/20000,0]. The proof sums the
quadratically small diagonal drift and uses the induced half-contraction
of the off-diagonal coordinate. -/
theorem schurStateBox_coarse_invariant_of_recursion
    (a b : ℕ → ℝ) (lambda : ℝ)
    (ha0 : |a 0| ≤ (1 / 500 : ℝ))
    (hb0_lower : -(1 / 20000 : ℝ) ≤ b 0)
    (hb0_upper : b 0 ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ))
    (ha_step : ∀ n,
      a (n + 1) =
        schurNextDiagonal (a n) (b n)
          (schurMidpointPivot (a n) (b n) lambda))
    (hb_step : ∀ n,
      b (n + 1) =
        schurNextOffDiagonal (b n)
          (schurMidpointPivot (a n) (b n) lambda)) :
    ∀ n, |a n| ≤ (1 / 400 : ℝ) ∧
      -(1 / 20000 : ℝ) ≤ b n ∧ b n ≤ 0 := by
  have hb0_abs : |b 0| ≤ (1 / 20000 : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact hb0_lower
    · exact le_trans hb0_upper (by norm_num)
  have hsq_abs (x : ℝ) : (|x|) ^ 2 = x ^ 2 := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      ring
  have hprefix : ∀ n, ∀ k ≤ n,
      |a k| ≤ (1 / 400 : ℝ) ∧
        -(1 / 20000 : ℝ) ≤ b k ∧ b k ≤ 0 := by
    intro n
    induction n with
    | zero =>
        intro k hk
        have hk0 : k = 0 := by omega
        subst k
        have ha0_box : |a 0| ≤ (1 / 400 : ℝ) :=
          le_trans ha0 (by norm_num)
        exact ⟨ha0_box, hb0_lower, hb0_upper⟩
    | succ n ih =>
        intro k hk
        by_cases hk_old : k ≤ n
        · exact ih k hk_old
        · have hk_eq : k = n + 1 := by omega
          subst k
          have hstate_n :
              |a n| ≤ (1 / 400 : ℝ) ∧
                -(1 / 20000 : ℝ) ≤ b n ∧ b n ≤ 0 :=
            ih n le_rfl
          have hu_nonneg : ∀ j, j ≤ n + 1 → 0 ≤ |b j| := by
            intro j hj
            exact abs_nonneg (b j)
          have hcontract_prefix : ∀ j, j < n + 1 →
              |b (j + 1)| ≤ (1 / 2 : ℝ) * |b j| := by
            intro j hj
            have hj_le : j ≤ n := by omega
            have hstate_j := ih j hj_le
            have ha_j_bounds := abs_le.mp hstate_j.1
            have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b j := by
              have hscale :
                  -(1 / 100 : ℝ) ≤ -(1 / 20000 : ℝ) := by norm_num
              exact le_trans hscale hstate_j.2.1
            have hc_lower :
                (13 / 10 : ℝ) ≤
                  schurMidpointPivot (a j) (b j) lambda := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.1, hstate_j.2.2, hlambda_lower]
            have hc_upper :
                schurMidpointPivot (a j) (b j) lambda ≤
                  (132 / 100 : ℝ) := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.2, hstate_j.2.1, hlambda_upper]
            have hc3_lower :
                (13 / 10 : ℝ) ≤
                  schurMidpointPivot (a j) (b j) lambda + 3 * b j := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.1, hstate_j.2.1, hlambda_lower]
            have hquadratic :=
              schurNextOffDiagonal_abs_le_four_fifths_sq_of_box
                (b j) (schurMidpointPivot (a j) (b j) lambda)
                hb_coarse_lower hstate_j.2.2
                hc_lower hc_upper hc3_lower
            have hnext_interval :=
              schurNextOffDiagonal_signed_interval_of_coarse_box
                (b j) (schurMidpointPivot (a j) (b j) lambda)
                hstate_j.2.1 hstate_j.2.2
                hc_lower hc_upper hc3_lower
            have hb_mag_nonneg : 0 ≤ -(b j) := by
              linarith [hstate_j.2.2]
            have hb_mag_upper : -(b j) ≤ (1 / 20000 : ℝ) := by
              linarith [hstate_j.2.1]
            have hbsq :
                (b j) ^ 2 ≤ (1 / 20000 : ℝ) * (-(b j)) := by
              calc
                (b j) ^ 2 = (-(b j)) * (-(b j)) := by ring
                _ ≤ (1 / 20000 : ℝ) * (-(b j)) :=
                  mul_le_mul_of_nonneg_right hb_mag_upper hb_mag_nonneg
            have hcoeff :
                (4 / 5 : ℝ) * (1 / 20000 : ℝ) ≤ (1 / 2 : ℝ) := by
              norm_num
            calc
              |b (j + 1)| =
                  |schurNextOffDiagonal (b j)
                    (schurMidpointPivot (a j) (b j) lambda)| := by
                      rw [hb_step j]
              _ = -schurNextOffDiagonal (b j)
                    (schurMidpointPivot (a j) (b j) lambda) :=
                abs_of_nonpos hnext_interval.2
              _ ≤ (4 / 5 : ℝ) * (b j) ^ 2 := by
                have h := hquadratic
                rw [abs_of_nonpos hnext_interval.2] at h
                exact h
              _ ≤ (4 / 5 : ℝ) *
                  ((1 / 20000 : ℝ) * (-(b j))) :=
                mul_le_mul_of_nonneg_left hbsq (by norm_num)
              _ = ((4 / 5 : ℝ) * (1 / 20000 : ℝ)) *
                  (-(b j)) := by ring
              _ ≤ (1 / 2 : ℝ) * (-(b j)) :=
                mul_le_mul_of_nonneg_right hcoeff hb_mag_nonneg
              _ = (1 / 2 : ℝ) * |b j| := by
                rw [abs_of_nonpos hstate_j.2.2]
          have hdiagonal_prefix : ∀ j, j < n + 1 →
              |a (j + 1) - a j| ≤ 2 * (|b j|) ^ 2 := by
            intro j hj
            have hj_le : j ≤ n := by omega
            have hstate_j := ih j hj_le
            have ha_j_bounds := abs_le.mp hstate_j.1
            have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b j := by
              have hscale :
                  -(1 / 100 : ℝ) ≤ -(1 / 20000 : ℝ) := by norm_num
              exact le_trans hscale hstate_j.2.1
            have hc_lower :
                (13 / 10 : ℝ) ≤
                  schurMidpointPivot (a j) (b j) lambda := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.1, hstate_j.2.2, hlambda_lower]
            have hc_upper :
                schurMidpointPivot (a j) (b j) lambda ≤
                  (132 / 100 : ℝ) := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.2, hstate_j.2.1, hlambda_upper]
            have hc3_lower :
                (13 / 10 : ℝ) ≤
                  schurMidpointPivot (a j) (b j) lambda + 3 * b j := by
              unfold schurMidpointPivot
              nlinarith [ha_j_bounds.1, hstate_j.2.1, hlambda_lower]
            have hlocal :=
              schurNextDiagonal_change_abs_le_two_mul_sq_of_box
                (a j) (b j)
                (schurMidpointPivot (a j) (b j) lambda)
                hb_coarse_lower hstate_j.2.2
                hc_lower hc_upper hc3_lower
            calc
              |a (j + 1) - a j| =
                  |schurNextDiagonal (a j) (b j)
                    (schurMidpointPivot (a j) (b j) lambda) - a j| := by
                      rw [ha_step j]
              _ ≤ 2 * (b j) ^ 2 := hlocal
              _ = 2 * (|b j|) ^ 2 := by rw [← hsq_abs (b j)]
          have hdrift :=
            diagonal_drift_total_le_four_mul_initial_sq_until
              (fun j => |b j|) a (n + 1)
              hu_nonneg hcontract_prefix hdiagonal_prefix
          have hbsq0 :
              (|b 0|) ^ 2 ≤ (1 / 20000 : ℝ) ^ 2 := by
            nlinarith [hb0_abs, abs_nonneg (b 0)]
          have hdrift_upper :
              |a (n + 1) - a 0| ≤
                4 * (1 / 20000 : ℝ) ^ 2 := by
            calc
              |a (n + 1) - a 0| ≤ 4 * (|b 0|) ^ 2 := hdrift
              _ ≤ 4 * (1 / 20000 : ℝ) ^ 2 := by nlinarith [hbsq0]
          have habs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
            apply abs_le.mpr
            constructor
            · calc
                -(|x| + |y|) = (-|x|) + (-|y|) := by ring
                _ ≤ x + y := add_le_add (neg_abs_le x) (neg_abs_le y)
            · exact add_le_add (le_abs_self x) (le_abs_self y)
          have ha_new : |a (n + 1)| ≤ (1 / 400 : ℝ) := by
            calc
              |a (n + 1)| =
                  |(a (n + 1) - a 0) + a 0| := by congr 1; ring
              _ ≤ |a (n + 1) - a 0| + |a 0| :=
                habs_add _ _
              _ ≤ 4 * (1 / 20000 : ℝ) ^ 2 + (1 / 500 : ℝ) :=
                add_le_add hdrift_upper ha0
              _ ≤ (1 / 400 : ℝ) := by norm_num
          have ha_n_bounds := abs_le.mp hstate_n.1
          have hc_lower :
              (13 / 10 : ℝ) ≤
                schurMidpointPivot (a n) (b n) lambda := by
            unfold schurMidpointPivot
            nlinarith [ha_n_bounds.1, hstate_n.2.2, hlambda_lower]
          have hc_upper :
              schurMidpointPivot (a n) (b n) lambda ≤
                (132 / 100 : ℝ) := by
            unfold schurMidpointPivot
            nlinarith [ha_n_bounds.2, hstate_n.2.1, hlambda_upper]
          have hc3_lower :
              (13 / 10 : ℝ) ≤
                schurMidpointPivot (a n) (b n) lambda + 3 * b n := by
            unfold schurMidpointPivot
            nlinarith [ha_n_bounds.1, hstate_n.2.1, hlambda_lower]
          have hb_new :=
            schurNextOffDiagonal_signed_interval_of_coarse_box
              (b n) (schurMidpointPivot (a n) (b n) lambda)
              hstate_n.2.1 hstate_n.2.2
              hc_lower hc_upper hc3_lower
          rw [← hb_step n] at hb_new
          exact ⟨ha_new, hb_new.1, hb_new.2⟩
  intro n
  exact hprefix n n le_rfl


/-- The concrete Schur trajectory inherits the coarse invariant state
box from any initial state in the level-three starting box. -/
theorem schurBoundaryTrajectory_coarse_state_box
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (1 / 500 : ℝ))
    (hb₀_lower : -(1 / 20000 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    ∀ n, |(schurBoundaryTrajectory lambda (a₀, b₀) n).1| ≤
        (1 / 400 : ℝ) ∧
      -(1 / 20000 : ℝ) ≤
        (schurBoundaryTrajectory lambda (a₀, b₀) n).2 ∧
      (schurBoundaryTrajectory lambda (a₀, b₀) n).2 ≤ 0 := by
  let a : ℕ → ℝ := fun n =>
    (schurBoundaryTrajectory lambda (a₀, b₀) n).1
  let b : ℕ → ℝ := fun n =>
    (schurBoundaryTrajectory lambda (a₀, b₀) n).2
  have ha_step : ∀ n,
      a (n + 1) =
        schurNextDiagonal (a n) (b n)
          (schurMidpointPivot (a n) (b n) lambda) := by
    intro n
    rfl
  have hb_step : ∀ n,
      b (n + 1) =
        schurNextOffDiagonal (b n)
          (schurMidpointPivot (a n) (b n) lambda) := by
    intro n
    rfl
  have hstate :=
    schurStateBox_coarse_invariant_of_recursion
      a b lambda ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper ha_step hb_step
  intro n
  simpa [a, b] using hstate n


/-- At a fixed parameter in the spectral window and inside the invariant
state box, one Schur step increases the A1 boundary characteristic by a
nonnegative amount no larger than twice the magnitude of the old
off-diagonal coefficient. -/
theorem schurNextA1_increment_bounds_of_state_box
    (a b lambda : ℝ)
    (ha_lower : -(1 / 10 ^ 35 : ℝ) ≤ a)
    (ha_upper : a ≤ (1 / 10 ^ 35 : ℝ))
    (hb_lower : -(6 / 10 ^ 37 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda) :
    0 ≤
        (schurNextDiagonal a b (schurMidpointPivot a b lambda) +
          2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda)) -
          (a + 2 * b) ∧
      (schurNextDiagonal a b (schurMidpointPivot a b lambda) +
        2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda)) -
          (a + 2 * b) ≤ 2 * (-b) := by
  have hc_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_upper, hlambda_lower]
  have hc3_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda + 3 * b := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  have hc_pos : 0 < schurMidpointPivot a b lambda :=
    lt_of_lt_of_le (by norm_num) hc_lower
  have hc3_pos :
      0 < schurMidpointPivot a b lambda + 3 * b :=
    lt_of_lt_of_le (by norm_num) hc3_lower
  have hnum_pos : 0 < lambda + 2 * (a + 2 * b) := by
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  have hden_pos :
      0 < lambda + 2 * (a + 2 * b) - 2 * b := by
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  have hratio_pos :
      0 < (lambda + 2 * (a + 2 * b)) /
        (lambda + 2 * (a + 2 * b) - 2 * b) :=
    div_pos hnum_pos hden_pos
  have hratio_le :
      (lambda + 2 * (a + 2 * b)) /
        (lambda + 2 * (a + 2 * b) - 2 * b) ≤ 1 := by
    apply (div_le_iff₀ hden_pos).2
    nlinarith [hb_upper]
  have hupdate :=
    schurNextA1_midpoint_update a b lambda
      (ne_of_gt hc_pos) (ne_of_gt hc3_pos)
  have hincrement :
      (schurNextDiagonal a b (schurMidpointPivot a b lambda) +
        2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda)) -
          (a + 2 * b) =
        (-2 * b) *
          ((lambda + 2 * (a + 2 * b)) /
            (lambda + 2 * (a + 2 * b) - 2 * b)) := by
    rw [hupdate]
    ring
  constructor
  · rw [hincrement]
    exact mul_nonneg (by linarith [hb_upper]) (le_of_lt hratio_pos)
  · rw [hincrement]
    have hfactor : 0 ≤ -2 * b := by linarith [hb_upper]
    calc
      (-2 * b) *
          ((lambda + 2 * (a + 2 * b)) /
            (lambda + 2 * (a + 2 * b) - 2 * b))
          ≤ (-2 * b) * 1 :=
        mul_le_mul_of_nonneg_left hratio_le hfactor
      _ = 2 * (-b) := by ring


/-- On the level-three coarse state box, a single Schur step changes
the A1 boundary characteristic by a nonnegative amount at most twice
the magnitude of the old off-diagonal coefficient. -/
theorem schurNextA1_increment_bounds_of_coarse_state_box
    (a b lambda : ℝ)
    (ha_lower : -(1 / 400 : ℝ) ≤ a)
    (hb_lower : -(1 / 20000 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda) :
    0 ≤
        (schurNextDiagonal a b (schurMidpointPivot a b lambda) +
          2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda)) -
          (a + 2 * b) ∧
      (schurNextDiagonal a b (schurMidpointPivot a b lambda) +
        2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda)) -
          (a + 2 * b) ≤ 2 * (-b) := by
  have hc_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_upper, hlambda_lower]
  have hc3_lower :
      (13 / 10 : ℝ) ≤ schurMidpointPivot a b lambda + 3 * b := by
    unfold schurMidpointPivot
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  have hc_pos : 0 < schurMidpointPivot a b lambda :=
    lt_of_lt_of_le (by norm_num) hc_lower
  have hc3_pos :
      0 < schurMidpointPivot a b lambda + 3 * b :=
    lt_of_lt_of_le (by norm_num) hc3_lower
  have hnum_pos : 0 < lambda + 2 * (a + 2 * b) := by
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  have hden_pos :
      0 < lambda + 2 * (a + 2 * b) - 2 * b := by
    nlinarith [ha_lower, hb_lower, hlambda_lower]
  have hratio_pos :
      0 < (lambda + 2 * (a + 2 * b)) /
        (lambda + 2 * (a + 2 * b) - 2 * b) :=
    div_pos hnum_pos hden_pos
  have hratio_le :
      (lambda + 2 * (a + 2 * b)) /
        (lambda + 2 * (a + 2 * b) - 2 * b) ≤ 1 := by
    apply (div_le_iff₀ hden_pos).2
    nlinarith [hb_upper]
  have hupdate :=
    schurNextA1_midpoint_update a b lambda
      (ne_of_gt hc_pos) (ne_of_gt hc3_pos)
  have hincrement :
      (schurNextDiagonal a b (schurMidpointPivot a b lambda) +
        2 * schurNextOffDiagonal b (schurMidpointPivot a b lambda)) -
          (a + 2 * b) =
        (-2 * b) *
          ((lambda + 2 * (a + 2 * b)) /
            (lambda + 2 * (a + 2 * b) - 2 * b)) := by
    rw [hupdate]
    ring
  constructor
  · rw [hincrement]
    exact mul_nonneg (by linarith [hb_upper]) (le_of_lt hratio_pos)
  · rw [hincrement]
    have hfactor : 0 ≤ -2 * b := by linarith [hb_upper]
    calc
      (-2 * b) *
          ((lambda + 2 * (a + 2 * b)) /
            (lambda + 2 * (a + 2 * b) - 2 * b))
          ≤ (-2 * b) * 1 :=
        mul_le_mul_of_nonneg_left hratio_le hfactor
      _ = 2 * (-b) := by ring


/-- The one-step off-diagonal update is at least a half-contraction
in absolute value throughout the level-three coarse box. -/
theorem schurNextOffDiagonal_half_contract_of_coarse_box
    (b c : ℝ)
    (hb_lower : -(1 / 20000 : ℝ) ≤ b)
    (hb_upper : b ≤ 0)
    (hc_lower : (13 / 10 : ℝ) ≤ c)
    (hc_upper : c ≤ (132 / 100 : ℝ))
    (hc3_lower : (13 / 10 : ℝ) ≤ c + 3 * b) :
    |schurNextOffDiagonal b c| ≤ (1 / 2 : ℝ) * |b| := by
  have hb_coarse_lower : -(1 / 100 : ℝ) ≤ b := by
    have hscale : -(1 / 100 : ℝ) ≤ -(1 / 20000 : ℝ) := by
      norm_num
    exact le_trans hscale hb_lower
  have hquadratic :=
    schurNextOffDiagonal_abs_le_four_fifths_sq_of_box
      b c hb_coarse_lower hb_upper hc_lower hc_upper hc3_lower
  have hb_mag_nonneg : 0 ≤ -b := by linarith
  have hb_mag_upper : -b ≤ (1 / 20000 : ℝ) := by linarith
  have hbsq : b ^ 2 ≤ (1 / 20000 : ℝ) * (-b) := by
    calc
      b ^ 2 = (-b) * (-b) := by ring
      _ ≤ (1 / 20000 : ℝ) * (-b) :=
        mul_le_mul_of_nonneg_right hb_mag_upper hb_mag_nonneg
  have hcoeff :
      (4 / 5 : ℝ) * (1 / 20000 : ℝ) ≤ (1 / 2 : ℝ) := by
    norm_num
  calc
    |schurNextOffDiagonal b c|
        ≤ (4 / 5 : ℝ) * b ^ 2 := hquadratic
    _ ≤ (4 / 5 : ℝ) *
        ((1 / 20000 : ℝ) * (-b)) :=
      mul_le_mul_of_nonneg_left hbsq (by norm_num)
    _ = ((4 / 5 : ℝ) * (1 / 20000 : ℝ)) * (-b) := by ring
    _ ≤ (1 / 2 : ℝ) * (-b) :=
      mul_le_mul_of_nonneg_right hcoeff hb_mag_nonneg
    _ = (1 / 2 : ℝ) * |b| := by
      rw [abs_of_nonpos hb_upper]


/-- Along every trajectory starting in the level-three coarse box, each
Schur step contracts the off-diagonal magnitude by at least one half. -/
theorem schurBoundaryTrajectory_coarse_offDiagonal_half_contract
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (1 / 500 : ℝ))
    (hb₀_lower : -(1 / 20000 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    ∀ n,
      |(schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).2| ≤
        (1 / 2 : ℝ) *
          |(schurBoundaryTrajectory lambda (a₀, b₀) n).2| := by
  intro n
  have hstate :=
    schurBoundaryTrajectory_coarse_state_box lambda a₀ b₀
      ha₀ hb₀_lower hb₀_upper hlambda_lower hlambda_upper n
  have ha_bounds := abs_le.mp hstate.1
  have hc_lower :
      (13 / 10 : ℝ) ≤
        schurMidpointPivot
          (schurBoundaryTrajectory lambda (a₀, b₀) n).1
          (schurBoundaryTrajectory lambda (a₀, b₀) n).2
          lambda := by
    unfold schurMidpointPivot
    nlinarith [ha_bounds.1, hstate.2.2, hlambda_lower]
  have hc_upper :
      schurMidpointPivot
          (schurBoundaryTrajectory lambda (a₀, b₀) n).1
          (schurBoundaryTrajectory lambda (a₀, b₀) n).2
          lambda ≤ (132 / 100 : ℝ) := by
    unfold schurMidpointPivot
    nlinarith [ha_bounds.2, hstate.2.1, hlambda_upper]
  have hc3_lower :
      (13 / 10 : ℝ) ≤
        schurMidpointPivot
            (schurBoundaryTrajectory lambda (a₀, b₀) n).1
            (schurBoundaryTrajectory lambda (a₀, b₀) n).2
            lambda +
          3 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2 := by
    unfold schurMidpointPivot
    nlinarith [ha_bounds.1, hstate.2.1, hlambda_lower]
  have hlocal :=
    schurNextOffDiagonal_half_contract_of_coarse_box
      (schurBoundaryTrajectory lambda (a₀, b₀) n).2
      (schurMidpointPivot
        (schurBoundaryTrajectory lambda (a₀, b₀) n).1
        (schurBoundaryTrajectory lambda (a₀, b₀) n).2
        lambda)
      hstate.2.1 hstate.2.2 hc_lower hc_upper hc3_lower
  simpa [schurBoundaryTrajectory, schurBoundaryStateStep] using hlocal


/-- Along every trajectory starting in the level-three coarse box, the A1
boundary characteristic is monotone and its one-step increase is bounded
by twice the current off-diagonal magnitude. -/
theorem schurBoundaryTrajectory_coarse_A1_increment_bounds
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (1 / 500 : ℝ))
    (hb₀_lower : -(1 / 20000 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    ∀ n,
      0 ≤
        ((schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).1 +
          2 * (schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).2) -
          ((schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
            2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2) ∧
      ((schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).1 +
          2 * (schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).2) -
        ((schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
          2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2) ≤
        2 * |(schurBoundaryTrajectory lambda (a₀, b₀) n).2| := by
  intro n
  have hstate :=
    schurBoundaryTrajectory_coarse_state_box lambda a₀ b₀
      ha₀ hb₀_lower hb₀_upper hlambda_lower hlambda_upper n
  have ha_lower := (abs_le.mp hstate.1).1
  have hlocal :=
    schurNextA1_increment_bounds_of_coarse_state_box
      (schurBoundaryTrajectory lambda (a₀, b₀) n).1
      (schurBoundaryTrajectory lambda (a₀, b₀) n).2
      lambda ha_lower hstate.2.1 hstate.2.2 hlambda_lower
  change
    0 ≤
      (schurNextDiagonal
          (schurBoundaryTrajectory lambda (a₀, b₀) n).1
          (schurBoundaryTrajectory lambda (a₀, b₀) n).2
          (schurMidpointPivot
            (schurBoundaryTrajectory lambda (a₀, b₀) n).1
            (schurBoundaryTrajectory lambda (a₀, b₀) n).2 lambda) +
        2 * schurNextOffDiagonal
          (schurBoundaryTrajectory lambda (a₀, b₀) n).2
          (schurMidpointPivot
            (schurBoundaryTrajectory lambda (a₀, b₀) n).1
            (schurBoundaryTrajectory lambda (a₀, b₀) n).2 lambda)) -
      ((schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
        2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2) ∧
    (schurNextDiagonal
          (schurBoundaryTrajectory lambda (a₀, b₀) n).1
          (schurBoundaryTrajectory lambda (a₀, b₀) n).2
          (schurMidpointPivot
            (schurBoundaryTrajectory lambda (a₀, b₀) n).1
            (schurBoundaryTrajectory lambda (a₀, b₀) n).2 lambda) +
        2 * schurNextOffDiagonal
          (schurBoundaryTrajectory lambda (a₀, b₀) n).2
          (schurMidpointPivot
            (schurBoundaryTrajectory lambda (a₀, b₀) n).1
            (schurBoundaryTrajectory lambda (a₀, b₀) n).2 lambda)) -
      ((schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
        2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2) ≤
      2 * |(schurBoundaryTrajectory lambda (a₀, b₀) n).2|
  constructor
  · exact hlocal.1
  · rw [abs_of_nonpos hstate.2.2]
    exact hlocal.2


/-- Finite sums of half-powers are bounded by the geometric limit two. -/
private theorem half_power_sum_le_two (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k) ≤ 2 := by
  have htail : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) +
        2 * (1 / 2 : ℝ) ^ n ≤ 2 := by
    intro n
    induction n with
    | zero =>
        norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
        nlinarith
  have htailN := htail N
  have hnonneg : 0 ≤ 2 * (1 / 2 : ℝ) ^ N := by positivity
  linarith


/-- A nonnegative sequence contracting by one half has every finite
partial sum bounded by twice its initial value. -/
theorem sum_range_le_two_mul_initial_of_half_contraction
    (u : ℕ → ℝ) (N : ℕ)
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hcontract : ∀ n, u (n + 1) ≤ (1 / 2 : ℝ) * u n) :
    (∑ k ∈ Finset.range N, u k) ≤ 2 * u 0 := by
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
  calc
    (∑ k ∈ Finset.range N, u k)
        ≤ ∑ k ∈ Finset.range N, u 0 * (1 / 2 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          exact hpoint k
    _ = u 0 * (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k) := by
          rw [← Finset.mul_sum]
    _ ≤ u 0 * 2 :=
      mul_le_mul_of_nonneg_left (half_power_sum_le_two N) (hu_nonneg 0)
    _ = 2 * u 0 := by ring


/-- A quarter-contractive nonnegative sequence has a finite partial sum
bounded by four thirds of its initial value. The proof retains the
remaining geometric tail in its induction invariant. -/
theorem sum_range_le_four_thirds_initial_of_quarter_contraction
    (u : ℕ → ℝ) (N : ℕ)
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hcontract : ∀ n, u (n + 1) ≤ (1 / 4 : ℝ) * u n) :
    (∑ k ∈ Finset.range N, u k) ≤ (4 / 3 : ℝ) * u 0 := by
  have htail : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, u k) +
        (4 / 3 : ℝ) * u n ≤ (4 / 3 : ℝ) * u 0 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        calc
          (∑ k ∈ Finset.range n, u k) + u n +
              (4 / 3 : ℝ) * u (n + 1)
              = (∑ k ∈ Finset.range n, u k) +
                  (u n + (4 / 3 : ℝ) * u (n + 1)) := by ring
          _ ≤ (∑ k ∈ Finset.range n, u k) +
                (4 / 3 : ℝ) * u n := by
                nlinarith [hcontract n]
          _ ≤ (4 / 3 : ℝ) * u 0 := ih
  have htailN := htail N
  have hlast_nonneg : 0 ≤ (4 / 3 : ℝ) * u N :=
    mul_nonneg (by norm_num) (hu_nonneg N)
  linarith


/-- The sum of successive increments of a real sequence telescopes. -/
private theorem sum_range_step_difference_eq
    (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (f (k + 1) - f k)) = f N - f 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring


/-- For a fixed parameter in [1.309,1.31] and an initial state in the
level-six box, every exact Schur step has a nonnegative A1-characteristic
increment bounded by twice the old off-diagonal magnitude. -/
theorem schurBoundaryTrajectory_A1_increment_bounds
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (3 / 10 ^ 36 : ℝ))
    (hb₀_lower : -(6 / 10 ^ 37 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    ∀ n,
      0 ≤
        ((schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).1 +
            2 * (schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).2) -
          ((schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
            2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2) ∧
      ((schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).1 +
          2 * (schurBoundaryTrajectory lambda (a₀, b₀) (n + 1)).2) -
        ((schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
          2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2) ≤
        2 * |(schurBoundaryTrajectory lambda (a₀, b₀) n).2| := by
  intro n
  have hstate :=
    schurBoundaryTrajectory_state_box
      lambda a₀ b₀ ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper n
  have ha_bounds := abs_le.mp hstate.1
  have hlocal :=
    schurNextA1_increment_bounds_of_state_box
      (schurBoundaryTrajectory lambda (a₀, b₀) n).1
      (schurBoundaryTrajectory lambda (a₀, b₀) n).2
      lambda ha_bounds.1 ha_bounds.2 hstate.2.1 hstate.2.2 hlambda_lower
  let f : ℕ → ℝ := fun k =>
    (schurBoundaryTrajectory lambda (a₀, b₀) k).1 +
      2 * (schurBoundaryTrajectory lambda (a₀, b₀) k).2
  have hmono : f n ≤ f (n + 1) := by
    simpa [f, schurBoundaryTrajectory, schurBoundaryStateStep] using hlocal.1
  have hupper_diff :
      f (n + 1) - f n ≤
        2 * (-(schurBoundaryTrajectory lambda (a₀, b₀) n).2) := by
    simpa [f, schurBoundaryTrajectory, schurBoundaryStateStep] using hlocal.2
  have hb_abs :
      |(schurBoundaryTrajectory lambda (a₀, b₀) n).2| =
        -(schurBoundaryTrajectory lambda (a₀, b₀) n).2 :=
    abs_of_nonpos hstate.2.2
  constructor
  · change 0 ≤ f (n + 1) - f n
    exact sub_nonneg.mpr hmono
  · change f (n + 1) - f n ≤
      2 * |(schurBoundaryTrajectory lambda (a₀, b₀) n).2|
    rw [hb_abs]
    exact hupper_diff


/-- From a level-three coarse initial state, the total increase of the
A1 characteristic over any finite number of Schur steps is at most four
times the initial off-diagonal magnitude. This finite-tail estimate will
be shifted to arbitrary starting levels to obtain the Cauchy criterion. -/
theorem schurBoundaryTrajectory_coarse_A1_total_increment_bound
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (1 / 500 : ℝ))
    (hb₀_lower : -(1 / 20000 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ)) :
    ∀ N,
      0 ≤
        ((schurBoundaryTrajectory lambda (a₀, b₀) N).1 +
          2 * (schurBoundaryTrajectory lambda (a₀, b₀) N).2) -
        (a₀ + 2 * b₀) ∧
      ((schurBoundaryTrajectory lambda (a₀, b₀) N).1 +
          2 * (schurBoundaryTrajectory lambda (a₀, b₀) N).2) -
        (a₀ + 2 * b₀) ≤ 4 * |b₀| := by
  let f : ℕ → ℝ := fun n =>
    (schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
      2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2
  let u : ℕ → ℝ := fun n =>
    |(schurBoundaryTrajectory lambda (a₀, b₀) n).2|
  have hu_nonneg : ∀ n, 0 ≤ u n := by
    intro n
    exact abs_nonneg _
  have hu_contract :=
    schurBoundaryTrajectory_coarse_offDiagonal_half_contract
      lambda a₀ b₀ ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper
  have hsum_u (N : ℕ) :
      (∑ k ∈ Finset.range N, u k) ≤ 2 * u 0 :=
    sum_range_le_two_mul_initial_of_half_contraction
      u N hu_nonneg (by
        intro n
        simpa [u] using hu_contract n)
  have hinc :=
    schurBoundaryTrajectory_coarse_A1_increment_bounds
      lambda a₀ b₀ ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper
  have hsum_inc_nonneg (N : ℕ) :
      0 ≤ ∑ k ∈ Finset.range N, (f (k + 1) - f k) := by
    apply Finset.sum_nonneg
    intro k hk
    simpa [f] using (hinc k).1
  have hsum_inc_upper (N : ℕ) :
      (∑ k ∈ Finset.range N, (f (k + 1) - f k)) ≤
        2 * (∑ k ∈ Finset.range N, u k) := by
    calc
      (∑ k ∈ Finset.range N, (f (k + 1) - f k))
          ≤ ∑ k ∈ Finset.range N, 2 * u k := by
            apply Finset.sum_le_sum
            intro k hk
            simpa [f, u] using (hinc k).2
      _ = 2 * (∑ k ∈ Finset.range N, u k) := by
            rw [← Finset.mul_sum]
  have htel (N : ℕ) :
      (∑ k ∈ Finset.range N, (f (k + 1) - f k)) = f N - f 0 :=
    sum_range_step_difference_eq f N
  intro N
  have hlower : 0 ≤ f N - f 0 := by
    rw [← htel N]
    exact hsum_inc_nonneg N
  have hupper : f N - f 0 ≤ 4 * u 0 := by
    rw [← htel N]
    calc
      (∑ k ∈ Finset.range N, (f (k + 1) - f k))
          ≤ 2 * (∑ k ∈ Finset.range N, u k) := hsum_inc_upper N
      _ ≤ 2 * (2 * u 0) :=
        mul_le_mul_of_nonneg_left (hsum_u N) (by norm_num)
      _ = 4 * u 0 := by ring
  have hupper' : f N - f 0 ≤ 4 * |b₀| := by
    calc
      f N - f 0 ≤ 4 * u 0 := hupper
      _ = 4 * |b₀| := by simp [u, schurBoundaryTrajectory]
  change 0 ≤ f N - f 0 ∧ f N - f 0 ≤ 4 * |b₀|
  exact ⟨hlower, hupper'⟩


/-- The A1 characteristic stays nonnegative at every finite Schur level
if it is nonnegative in the initial state box. -/
theorem schurBoundaryTrajectory_A1_nonneg_of_initial_nonneg
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (3 / 10 ^ 36 : ℝ))
    (hb₀_lower : -(6 / 10 ^ 37 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ))
    (hf₀ : 0 ≤ a₀ + 2 * b₀) :
    ∀ n, 0 ≤
      (schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
        2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2 := by
  let f : ℕ → ℝ := fun n =>
    (schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
      2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2
  have hinc :=
    schurBoundaryTrajectory_A1_increment_bounds
      lambda a₀ b₀ ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper
  have hf₀' : 0 ≤ f 0 := by
    simpa [f, schurBoundaryTrajectory] using hf₀
  intro n
  induction n with
  | zero =>
      exact hf₀'
  | succ n ih =>
      have hstep : 0 ≤ f (n + 1) - f n := by
        simpa [f] using (hinc n).1
      linarith


/-- The upper A1 endpoint sign is also preserved at every finite level:
the total increase is at most 1.6e-36, strictly below a 1.7e-36
initial negative margin. This is a finite-level sign theorem, not yet a
continuity or root-existence theorem. -/
theorem schurBoundaryTrajectory_A1_neg_of_initial_margin
    (lambda a₀ b₀ : ℝ)
    (ha₀ : |a₀| ≤ (3 / 10 ^ 36 : ℝ))
    (hb₀_lower : -(6 / 10 ^ 37 : ℝ) ≤ b₀)
    (hb₀_upper : b₀ ≤ 0)
    (hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda)
    (hlambda_upper : lambda ≤ (131 / 100 : ℝ))
    (hf₀ : a₀ + 2 * b₀ ≤ -(17 / 10 ^ 37 : ℝ)) :
    ∀ n,
      (schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
        2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2 < 0 := by
  let f : ℕ → ℝ := fun n =>
    (schurBoundaryTrajectory lambda (a₀, b₀) n).1 +
      2 * (schurBoundaryTrajectory lambda (a₀, b₀) n).2
  let u : ℕ → ℝ := fun n =>
    |(schurBoundaryTrajectory lambda (a₀, b₀) n).2|
  have hstate_box :=
    schurBoundaryTrajectory_state_box
      lambda a₀ b₀ ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper
  have hu_nonneg : ∀ n, 0 ≤ u n := by
    intro n
    exact abs_nonneg _
  have hu_contract : ∀ n, u (n + 1) ≤ (1 / 4 : ℝ) * u n := by
    intro n
    have hstate := hstate_box n
    have ha_bounds := abs_le.mp hstate.1
    have hlinear :=
      schurNextOffDiagonal_abs_le_e_minus36_mul_abs_of_state_box
        (schurBoundaryTrajectory lambda (a₀, b₀) n).1
        (schurBoundaryTrajectory lambda (a₀, b₀) n).2
        lambda ha_bounds.1 ha_bounds.2 hstate.2.1 hstate.2.2
        hlambda_lower hlambda_upper
    calc
      u (n + 1) ≤ (1 / 10 ^ 36 : ℝ) * u n := by
        simpa [u, schurBoundaryTrajectory, schurBoundaryStateStep] using hlinear
      _ ≤ (1 / 4 : ℝ) * u n :=
        mul_le_mul_of_nonneg_right (by norm_num) (hu_nonneg n)
  have hsum_u (N : ℕ) :
      (∑ k ∈ Finset.range N, u k) ≤ (4 / 3 : ℝ) * u 0 :=
    sum_range_le_four_thirds_initial_of_quarter_contraction
      u N hu_nonneg hu_contract
  have hu₀_upper : u 0 ≤ (6 / 10 ^ 37 : ℝ) := by
    have hb₀_abs : |b₀| ≤ (6 / 10 ^ 37 : ℝ) := by
      apply abs_le.mpr
      constructor
      · exact hb₀_lower
      · exact le_trans hb₀_upper (by norm_num)
    simpa [u, schurBoundaryTrajectory] using hb₀_abs
  have hbudget (N : ℕ) :
      2 * (∑ k ∈ Finset.range N, u k) ≤ (16 / 10 ^ 37 : ℝ) := by
    have h := hsum_u N
    nlinarith [h, hu₀_upper]
  have hinc :=
    schurBoundaryTrajectory_A1_increment_bounds
      lambda a₀ b₀ ha₀ hb₀_lower hb₀_upper
      hlambda_lower hlambda_upper
  have hsum_increment_bound (N : ℕ) :
      (∑ k ∈ Finset.range N, (f (k + 1) - f k)) ≤
        2 * (∑ k ∈ Finset.range N, u k) := by
    calc
      (∑ k ∈ Finset.range N, (f (k + 1) - f k))
          ≤ ∑ k ∈ Finset.range N, 2 * u k := by
              apply Finset.sum_le_sum
              intro k hk
              simpa [f, u] using (hinc k).2
      _ = 2 * (∑ k ∈ Finset.range N, u k) := by
            rw [← Finset.mul_sum]
  have htel (N : ℕ) :
      (∑ k ∈ Finset.range N, (f (k + 1) - f k)) = f N - f 0 :=
    sum_range_step_difference_eq f N
  have hf₀' : f 0 ≤ -(17 / 10 ^ 37 : ℝ) := by
    simpa [f, schurBoundaryTrajectory] using hf₀
  intro N
  have hsumN := hsum_increment_bound N
  have hbudgetN := hbudget N
  have htelN := htel N
  have hupper : f N ≤ f 0 + (16 / 10 ^ 37 : ℝ) := by
    linarith
  have hstrict_margin : f N ≤ -(1 / 10 ^ 37 : ℝ) := by
    linarith
  have hnegative : f N < 0 :=
    lt_of_le_of_lt hstrict_margin (by norm_num)
  simpa [f] using hnegative


/-- Exact rational lower endpoint of the narrow level-six bootstrap window.
The 36 decimal digits are represented as an integer divided by 10^36. -/
noncomputable def schurBootstrapLambdaLower : ℝ :=
  (1309128920280813421888623088170810187 / 10 ^ 36 : ℝ)

/-- Exact rational upper endpoint of the narrow level-six bootstrap window. -/
noncomputable def schurBootstrapLambdaUpper : ℝ :=
  (1309128920280813421888623088170810189 / 10 ^ 36 : ℝ)

/-- The two fixed rational endpoints lie in the coarse parameter window
used by the conditional all-level Schur state-box theorem. -/
theorem schurBootstrapEndpoints_in_parameter_window :
    (1309 / 1000 : ℝ) ≤ schurBootstrapLambdaLower ∧
      schurBootstrapLambdaLower ≤ (131 / 100 : ℝ) ∧
    (1309 / 1000 : ℝ) ≤ schurBootstrapLambdaUpper ∧
      schurBootstrapLambdaUpper ≤ (131 / 100 : ℝ) := by
  norm_num [schurBootstrapLambdaLower, schurBootstrapLambdaUpper]

/-- Exact level-six starting enclosure and positive A1 sign at the lower
rational endpoint. This is computed from six exact Schur steps starting
from the original state (2-lambda,1), not from rounded decimal data. -/
theorem schurBootstrapLower_levelSix_certificate :
    |(schurBoundaryTrajectory schurBootstrapLambdaLower
        (2 - schurBootstrapLambdaLower, 1) 6).1| ≤
          (3 / 10 ^ 36 : ℝ) ∧
      -(6 / 10 ^ 37 : ℝ) ≤
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (2 - schurBootstrapLambdaLower, 1) 6).2 ∧
      (schurBoundaryTrajectory schurBootstrapLambdaLower
        (2 - schurBootstrapLambdaLower, 1) 6).2 ≤ 0 ∧
      0 <
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (2 - schurBootstrapLambdaLower, 1) 6).1 +
          2 * (schurBoundaryTrajectory schurBootstrapLambdaLower
            (2 - schurBootstrapLambdaLower, 1) 6).2 := by
  norm_num [schurBootstrapLambdaLower, schurBoundaryTrajectory,
    schurBoundaryStateStep, schurNextDiagonal, schurNextOffDiagonal,
    schurMidpointPivot]

/-- Exact level-six starting enclosure and strict negative A1 margin at
the upper rational endpoint. The margin is stronger than 1.7e-36, which
is the amount required by the finite-level sign-transport theorem. -/
theorem schurBootstrapUpper_levelSix_certificate :
    |(schurBoundaryTrajectory schurBootstrapLambdaUpper
        (2 - schurBootstrapLambdaUpper, 1) 6).1| ≤
          (3 / 10 ^ 36 : ℝ) ∧
      -(6 / 10 ^ 37 : ℝ) ≤
        (schurBoundaryTrajectory schurBootstrapLambdaUpper
          (2 - schurBootstrapLambdaUpper, 1) 6).2 ∧
      (schurBoundaryTrajectory schurBootstrapLambdaUpper
        (2 - schurBootstrapLambdaUpper, 1) 6).2 ≤ 0 ∧
      (schurBoundaryTrajectory schurBootstrapLambdaUpper
        (2 - schurBootstrapLambdaUpper, 1) 6).1 +
          2 * (schurBoundaryTrajectory schurBootstrapLambdaUpper
            (2 - schurBootstrapLambdaUpper, 1) 6).2 ≤
              -(17 / 10 ^ 37 : ℝ) := by
  norm_num [schurBootstrapLambdaUpper, schurBoundaryTrajectory,
    schurBoundaryStateStep, schurNextDiagonal, schurNextOffDiagonal,
    schurMidpointPivot]


/-- Combining the exact rational level-six certificates with the
conditional finite-level sign-transport lemmas gives opposite A1 signs at
the two fixed rational endpoints, at every finite Schur level. -/
theorem schurBootstrapEndpoints_A1_signs_all_finite_levels :
    (∀ n,
      0 ≤
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (schurBoundaryTrajectory schurBootstrapLambdaLower
            (2 - schurBootstrapLambdaLower, 1) 6) n).1 +
          2 * (schurBoundaryTrajectory schurBootstrapLambdaLower
            (schurBoundaryTrajectory schurBootstrapLambdaLower
              (2 - schurBootstrapLambdaLower, 1) 6) n).2) ∧
    (∀ n,
      (schurBoundaryTrajectory schurBootstrapLambdaUpper
        (schurBoundaryTrajectory schurBootstrapLambdaUpper
          (2 - schurBootstrapLambdaUpper, 1) 6) n).1 +
        2 * (schurBoundaryTrajectory schurBootstrapLambdaUpper
          (schurBoundaryTrajectory schurBootstrapLambdaUpper
            (2 - schurBootstrapLambdaUpper, 1) 6) n).2 < 0) := by
  have hwindow := schurBootstrapEndpoints_in_parameter_window
  have hlow := schurBootstrapLower_levelSix_certificate
  have hupp := schurBootstrapUpper_levelSix_certificate
  constructor
  · exact
      schurBoundaryTrajectory_A1_nonneg_of_initial_nonneg
        schurBootstrapLambdaLower
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (2 - schurBootstrapLambdaLower, 1) 6).1
        (schurBoundaryTrajectory schurBootstrapLambdaLower
          (2 - schurBootstrapLambdaLower, 1) 6).2
        hlow.1 hlow.2.1 hlow.2.2.1
        hwindow.1 hwindow.2.1 (le_of_lt hlow.2.2.2)
  · exact
      schurBoundaryTrajectory_A1_neg_of_initial_margin
        schurBootstrapLambdaUpper
        (schurBoundaryTrajectory schurBootstrapLambdaUpper
          (2 - schurBootstrapLambdaUpper, 1) 6).1
        (schurBoundaryTrajectory schurBootstrapLambdaUpper
          (2 - schurBootstrapLambdaUpper, 1) 6).2
        hupp.1 hupp.2.1 hupp.2.2.1
        hwindow.2.2.1 hwindow.2.2.2 hupp.2.2.2



/-- The next diagonal Schur coefficient is continuous at a parameter
whenever the input coordinates are continuous there and both scalar
Schur denominators are nonzero at that parameter. -/
theorem schurNextDiagonal_continuousAt
    (a b c : ℝ → ℝ) (x : ℝ)
    (ha : ContinuousAt a x)
    (hb : ContinuousAt b x)
    (hc : ContinuousAt c x)
    (hc0 : c x ≠ 0)
    (hc3 : c x + 3 * b x ≠ 0) :
    ContinuousAt
      (fun y => schurNextDiagonal (a y) (b y) (c y)) x := by
  have hcb : ContinuousAt (fun y => c y + b y) x := hc.add hb
  have hc3_cont : ContinuousAt (fun y => c y + 3 * b y) x :=
    hc.add (continuousAt_const.mul hb)
  have hden : ContinuousAt
      (fun y => c y * (c y + 3 * b y)) x :=
    hc.mul hc3_cont
  have hbsq : ContinuousAt (fun y => (b y) ^ 2) x := hb.pow 2
  have hnum2 : ContinuousAt (fun y => 2 * (b y) ^ 2) x :=
    continuousAt_const.mul hbsq
  have hnum : ContinuousAt
      (fun y => (2 * (b y) ^ 2) * (c y + b y)) x :=
    hnum2.mul hcb
  have hquot : ContinuousAt
      (fun y =>
        ((2 * (b y) ^ 2) * (c y + b y)) /
          (c y * (c y + 3 * b y))) x :=
    hnum.div hden (mul_ne_zero hc0 hc3)
  change ContinuousAt
    (fun y => a y -
      ((2 * (b y) ^ 2 * (c y + b y)) /
        (c y * (c y + 3 * b y)))) x
  exact ha.sub hquot


/-- The next off-diagonal Schur coefficient is continuous under the
same pointwise nonvanishing condition on the two Schur denominators. -/
theorem schurNextOffDiagonal_continuousAt
    (b c : ℝ → ℝ) (x : ℝ)
    (hb : ContinuousAt b x)
    (hc : ContinuousAt c x)
    (hc0 : c x ≠ 0)
    (hc3 : c x + 3 * b x ≠ 0) :
    ContinuousAt
      (fun y => schurNextOffDiagonal (b y) (c y)) x := by
  have hcb : ContinuousAt (fun y => c y - b y) x := hc.sub hb
  have hc3_cont : ContinuousAt (fun y => c y + 3 * b y) x :=
    hc.add (continuousAt_const.mul hb)
  have hden : ContinuousAt
      (fun y => c y * (c y + 3 * b y)) x :=
    hc.mul hc3_cont
  have hbsq : ContinuousAt (fun y => (b y) ^ 2) x := hb.pow 2
  have hneg_sq : ContinuousAt (fun y => -((b y) ^ 2)) x :=
    hbsq.neg
  have hnum : ContinuousAt
      (fun y => (-((b y) ^ 2)) * (c y - b y)) x :=
    hneg_sq.mul hcb
  have hquot : ContinuousAt
      (fun y =>
        ((-((b y) ^ 2)) * (c y - b y)) /
          (c y * (c y + 3 * b y))) x :=
    hnum.div hden (mul_ne_zero hc0 hc3)
  simpa [schurNextOffDiagonal] using hquot


/-- Both coordinates of the original Schur trajectory are continuous at
a fixed parameter through level n, provided every pivot denominator
encountered before level n is nonzero there. -/
theorem schurBoundaryTrajectory_pair_continuousAt_of_nonzero_pivots
    (lambda₀ : ℝ) :
    ∀ n : ℕ,
      (∀ k, k < n →
        schurMidpointPivot
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).1
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).2
          lambda₀ ≠ 0 ∧
        schurMidpointPivot
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).1
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).2
          lambda₀ +
            3 * (schurBoundaryTrajectory lambda₀
              (2 - lambda₀, 1) k).2 ≠ 0) →
      ContinuousAt
        (fun lambda =>
          (schurBoundaryTrajectory lambda (2 - lambda, 1) n).1)
        lambda₀ ∧
      ContinuousAt
        (fun lambda =>
          (schurBoundaryTrajectory lambda (2 - lambda, 1) n).2)
        lambda₀ := by
  intro n
  induction n with
  | zero =>
      intro hden
      constructor
      · change ContinuousAt (fun lambda : ℝ => 2 - lambda) lambda₀
        fun_prop
      · simpa [schurBoundaryTrajectory] using
          (continuousAt_const :
            ContinuousAt (fun _ : ℝ => (1 : ℝ)) lambda₀)
  | succ n ih =>
      intro hden
      have hprev := ih (by
        intro k hk
        exact hden k (by omega))
      let af : ℝ → ℝ := fun lambda =>
        (schurBoundaryTrajectory lambda (2 - lambda, 1) n).1
      let bf : ℝ → ℝ := fun lambda =>
        (schurBoundaryTrajectory lambda (2 - lambda, 1) n).2
      let cf : ℝ → ℝ := fun lambda =>
        schurMidpointPivot (af lambda) (bf lambda) lambda
      have hAprev : ContinuousAt af lambda₀ := by
        simpa [af] using hprev.1
      have hBprev : ContinuousAt bf lambda₀ := by
        simpa [bf] using hprev.2
      have htwoA : ContinuousAt (fun lambda => 2 * af lambda) lambda₀ :=
        continuousAt_const.mul hAprev
      have htwoA_add_lambda :
          ContinuousAt (fun lambda => 2 * af lambda + lambda) lambda₀ :=
        htwoA.add continuousAt_id
      have hC : ContinuousAt cf lambda₀ := by
        change ContinuousAt
          (fun lambda => 2 * af lambda + lambda - bf lambda) lambda₀
        exact htwoA_add_lambda.sub hBprev
      have hnonzero :
          cf lambda₀ ≠ 0 ∧ cf lambda₀ + 3 * bf lambda₀ ≠ 0 := by
        simpa [cf, af, bf] using hden n (by omega)
      have hA_next :=
        schurNextDiagonal_continuousAt af bf cf lambda₀
          hAprev hBprev hC hnonzero.1 hnonzero.2
      have hB_next :=
        schurNextOffDiagonal_continuousAt bf cf lambda₀
          hBprev hC hnonzero.1 hnonzero.2
      constructor
      · simpa [af, bf, cf, schurBoundaryTrajectory,
          schurBoundaryStateStep] using hA_next
      · simpa [af, bf, cf, schurBoundaryTrajectory,
          schurBoundaryStateStep] using hB_next


/-- The A1 characteristic at each finite level is continuous at any
parameter where the finitely many preceding Schur denominators are
nonzero. Uniform nonvanishing on the whole bootstrap interval remains
a separate hypothesis to be established. -/
theorem schurBoundaryTrajectory_A1_continuousAt_of_nonzero_pivots
    (lambda₀ : ℝ) (n : ℕ)
    (hden :
      ∀ k, k < n →
        schurMidpointPivot
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).1
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).2
          lambda₀ ≠ 0 ∧
        schurMidpointPivot
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).1
          (schurBoundaryTrajectory lambda₀ (2 - lambda₀, 1) k).2
          lambda₀ +
            3 * (schurBoundaryTrajectory lambda₀
              (2 - lambda₀, 1) k).2 ≠ 0) :
    ContinuousAt
      (fun lambda =>
        (schurBoundaryTrajectory lambda (2 - lambda, 1) n).1 +
          2 * (schurBoundaryTrajectory lambda (2 - lambda, 1) n).2)
      lambda₀ := by
  have hcoords :=
    schurBoundaryTrajectory_pair_continuousAt_of_nonzero_pivots
      lambda₀ n hden
  exact hcoords.1.add (continuousAt_const.mul hcoords.2)



/-- Schur trajectories satisfy the expected semigroup law in the level
index: taking m steps and then n more steps equals taking m+n steps. -/
theorem schurBoundaryTrajectory_add
    (lambda : ℝ) (initial : ℝ × ℝ) (m n : ℕ) :
    schurBoundaryTrajectory lambda initial (m + n) =
      schurBoundaryTrajectory lambda
        (schurBoundaryTrajectory lambda initial m) n := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, schurBoundaryTrajectory]
  | succ n ih =>
      simp only [Nat.add_succ, schurBoundaryTrajectory]
      exact congrArg (schurBoundaryStateStep lambda) ih


/-- The A1 characteristic at level 6+n, starting from the original
boundary state (2-lambda,1). -/
noncomputable def schurBootstrapA1AtLevel (lambda : ℝ) (n : ℕ) : ℝ :=
  (schurBoundaryTrajectory lambda (2 - lambda, 1) (6 + n)).1 +
    2 * (schurBoundaryTrajectory lambda (2 - lambda, 1) (6 + n)).2


/-- If all Schur denominators through a fixed finite level are nonzero
for every parameter in the bootstrap interval, the corresponding A1
characteristic is continuous on that interval. -/
theorem schurBootstrapA1AtLevel_continuousOn_of_nonzero_pivots
    (n : ℕ)
    (hden :
      ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
          schurBootstrapLambdaUpper →
        ∀ k, k < 6 + n →
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda ≠ 0 ∧
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda +
              3 * (schurBoundaryTrajectory lambda
                (2 - lambda, 1) k).2 ≠ 0) :
    ContinuousOn
      (fun lambda => schurBootstrapA1AtLevel lambda n)
      (Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) := by
  intro lambda hlambda
  have hcontinuous :=
    schurBoundaryTrajectory_A1_continuousAt_of_nonzero_pivots
      lambda (6 + n) (hden lambda hlambda)
  simpa [schurBootstrapA1AtLevel] using hcontinuous.continuousWithinAt


/-- Conditional finite-level root existence: the exact opposite endpoint
signs proved above, together with continuity (equivalently here, nonzero
Schur denominators along the interval), force an A1 root by IVT. -/
theorem schurBootstrapA1AtLevel_exists_root_of_nonzero_pivots
    (n : ℕ)
    (hden :
      ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
          schurBootstrapLambdaUpper →
        ∀ k, k < 6 + n →
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda ≠ 0 ∧
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda +
              3 * (schurBoundaryTrajectory lambda
                (2 - lambda, 1) k).2 ≠ 0) :
    ∃ lambda ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper,
      schurBootstrapA1AtLevel lambda n = 0 := by
  have hle :
      schurBootstrapLambdaLower ≤ schurBootstrapLambdaUpper := by
    norm_num [schurBootstrapLambdaLower, schurBootstrapLambdaUpper]
  have hcontinuous :=
    schurBootstrapA1AtLevel_continuousOn_of_nonzero_pivots n hden
  have hsigns := schurBootstrapEndpoints_A1_signs_all_finite_levels
  have hleft :
      0 ≤ schurBootstrapA1AtLevel schurBootstrapLambdaLower n := by
    simpa [schurBootstrapA1AtLevel, schurBoundaryTrajectory_add] using
      hsigns.1 n
  have hright :
      schurBootstrapA1AtLevel schurBootstrapLambdaUpper n < 0 := by
    simpa [schurBootstrapA1AtLevel, schurBoundaryTrajectory_add] using
      hsigns.2 n
  have hzero :
      (0 : ℝ) ∈ Set.Icc
        (schurBootstrapA1AtLevel schurBootstrapLambdaUpper n)
        (schurBootstrapA1AtLevel schurBootstrapLambdaLower n) :=
    ⟨le_of_lt hright, hleft⟩
  have himage := intermediate_value_Icc' hle hcontinuous
  rcases himage hzero with ⟨lambda, hlambda, hvalue⟩
  exact ⟨lambda, hlambda, hvalue⟩



/-- After the exact level-six state has entered the invariant Schur box,
all later scalar Schur denominators are automatically positive. Thus the
only remaining denominator checks are the finite prefix k<6. -/
theorem schurBootstrap_all_pivots_nonzero_of_levelSix_box_and_prefix
    (hlevelSix :
      ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
          schurBootstrapLambdaUpper →
        |(schurBoundaryTrajectory lambda (2 - lambda, 1) 6).1| ≤
            (3 / 10 ^ 36 : ℝ) ∧
        -(6 / 10 ^ 37 : ℝ) ≤
            (schurBoundaryTrajectory lambda (2 - lambda, 1) 6).2 ∧
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 6).2 ≤ 0)
    (hprefix :
      ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
          schurBootstrapLambdaUpper →
        ∀ k, k < 6 →
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda ≠ 0 ∧
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda +
              3 * (schurBoundaryTrajectory lambda
                (2 - lambda, 1) k).2 ≠ 0) :
    ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper →
      ∀ k,
        schurMidpointPivot
          (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
          (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
          lambda ≠ 0 ∧
        schurMidpointPivot
          (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
          (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
          lambda +
            3 * (schurBoundaryTrajectory lambda
              (2 - lambda, 1) k).2 ≠ 0 := by
  intro lambda hlambda k
  by_cases hk : k < 6
  · exact hprefix lambda hlambda k hk
  · have hkge : 6 ≤ k := by omega
    obtain ⟨m, hm⟩ : ∃ m, k = 6 + m := by
      refine ⟨k - 6, ?_⟩
      omega
    subst k
    have hwindow := schurBootstrapEndpoints_in_parameter_window
    have hlambda_lower :
        (1309 / 1000 : ℝ) ≤ lambda :=
      le_trans hwindow.1 hlambda.1
    have hlambda_upper :
        lambda ≤ (131 / 100 : ℝ) :=
      le_trans hlambda.2 hwindow.2.2.2
    have hstart := hlevelSix lambda hlambda
    have hstate :=
      schurBoundaryTrajectory_state_box lambda
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 6).1
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 6).2
        hstart.1 hstart.2.1 hstart.2.2
        hlambda_lower hlambda_upper m
    rw [schurBoundaryTrajectory_add lambda (2 - lambda, 1) 6 m]
    have ha_lower :=
      (abs_le.mp hstate.1).1
    have hc_lower :
        (13 / 10 : ℝ) ≤
          schurMidpointPivot
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).1
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).2
            lambda := by
      unfold schurMidpointPivot
      nlinarith [ha_lower, hstate.2.2, hlambda_lower]
    have hc3_lower :
        (13 / 10 : ℝ) ≤
          schurMidpointPivot
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).1
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).2
              lambda +
            3 * (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).2 := by
      unfold schurMidpointPivot
      nlinarith [ha_lower, hstate.2.1, hlambda_lower]
    have hc_pos :
        0 <
          schurMidpointPivot
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).1
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).2
            lambda :=
      lt_of_lt_of_le (by norm_num) hc_lower
    have hc3_pos :
        0 <
          schurMidpointPivot
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).1
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).2
              lambda +
            3 * (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 6) m).2 :=
      lt_of_lt_of_le (by norm_num) hc3_lower
    exact ⟨ne_of_gt hc_pos, ne_of_gt hc3_pos⟩


/-- The conditional IVT root theorem only needs a uniform level-six state
box and positivity of the six initial pivot pairs. The state-box invariant
then supplies every later denominator automatically. -/
theorem schurBootstrapA1AtLevel_exists_root_of_levelSix_box_and_prefix_pivots
    (n : ℕ)
    (hlevelSix :
      ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
          schurBootstrapLambdaUpper →
        |(schurBoundaryTrajectory lambda (2 - lambda, 1) 6).1| ≤
            (3 / 10 ^ 36 : ℝ) ∧
        -(6 / 10 ^ 37 : ℝ) ≤
            (schurBoundaryTrajectory lambda (2 - lambda, 1) 6).2 ∧
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 6).2 ≤ 0)
    (hprefix :
      ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
          schurBootstrapLambdaUpper →
        ∀ k, k < 6 →
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda ≠ 0 ∧
          schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda +
              3 * (schurBoundaryTrajectory lambda
                (2 - lambda, 1) k).2 ≠ 0) :
    ∃ lambda ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper,
      schurBootstrapA1AtLevel lambda n = 0 := by
  apply schurBootstrapA1AtLevel_exists_root_of_nonzero_pivots n
  intro lambda hlambda k hk
  exact
    schurBootstrap_all_pivots_nonzero_of_levelSix_box_and_prefix
      hlevelSix hprefix lambda hlambda k


/-- Closed form for the first diagonal Schur coefficient from the
original initial state (2-lambda,1). -/
noncomputable def schurLevelOneDiagonal (lambda : ℝ) : ℝ :=
  (2 - lambda) - 2 * (4 - lambda) / ((3 - lambda) * (6 - lambda))

/-- Closed form for the first off-diagonal Schur coefficient from the
original initial state (2-lambda,1). -/
noncomputable def schurLevelOneOffDiagonal (lambda : ℝ) : ℝ :=
  -(2 - lambda) / ((3 - lambda) * (6 - lambda))


/-- The original Schur trajectory at level one is exactly the two
closed-form rational functions above. -/
theorem schurBoundaryTrajectory_level_one_formula (lambda : ℝ) :
    schurBoundaryTrajectory lambda (2 - lambda, 1) 1 =
      (schurLevelOneDiagonal lambda,
        schurLevelOneOffDiagonal lambda) := by
  have hc :
      schurMidpointPivot (2 - lambda) 1 lambda = 3 - lambda := by
    simp [schurMidpointPivot]
    ring
  simp [schurBoundaryTrajectory, schurBoundaryStateStep, hc,
    schurNextDiagonal, schurNextOffDiagonal,
    schurLevelOneDiagonal, schurLevelOneOffDiagonal]
  constructor
  · rw [show 3 - lambda + 1 = 4 - lambda by ring,
      show 3 - lambda + 3 = 6 - lambda by ring]
  · rw [show 1 - (3 - lambda) = lambda - 2 by ring,
      show 3 - lambda + 3 = 6 - lambda by ring]


/-- Across the narrow bootstrap interval, the first diagonal coefficient
is decreasing and the first off-diagonal coefficient is increasing. -/
theorem schurBootstrap_levelOne_antitone_mono
    (x y : ℝ)
    (hx : x ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hy : y ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hxy : x ≤ y) :
    schurLevelOneDiagonal y ≤ schurLevelOneDiagonal x ∧
      schurLevelOneOffDiagonal x ≤ schurLevelOneOffDiagonal y := by
  have hwindow := schurBootstrapEndpoints_in_parameter_window
  have hx_lower : (1309 / 1000 : ℝ) ≤ x := le_trans hwindow.1 hx.1
  have hx_upper : x ≤ (131 / 100 : ℝ) :=
    le_trans hx.2 hwindow.2.2.2
  have hy_lower : (1309 / 1000 : ℝ) ≤ y := le_trans hwindow.1 hy.1
  have hy_upper : y ≤ (131 / 100 : ℝ) :=
    le_trans hy.2 hwindow.2.2.2
  have hx3 : 0 < 3 - x := by linarith
  have hx6 : 0 < 6 - x := by linarith
  have hy3 : 0 < 3 - y := by linarith
  have hy6 : 0 < 6 - y := by linarith
  have hden_pos :
      0 < (3 - x) * (6 - x) * (3 - y) * (6 - y) :=
    mul_pos (mul_pos (mul_pos hx3 hx6) hy3) hy6
  have hprod_lower :
      0 ≤ (x - (1309 / 1000 : ℝ)) *
        (y - (1309 / 1000 : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hx_lower)
      (sub_nonneg.mpr hy_lower)
  have hpolyA :
      0 < 18 - 4 * x - 4 * y + x * y := by
    nlinarith
  have hprod_upper :
      0 ≤ ((131 / 100 : ℝ) - x) *
        ((131 / 100 : ℝ) - y) :=
    mul_nonneg (sub_nonneg.mpr hx_upper)
      (sub_nonneg.mpr hy_upper)
  have hpolyB :
      0 < 2 * x + 2 * y - x * y := by
    nlinarith
  have hquotA :
      0 < (18 - 4 * x - 4 * y + x * y) /
        ((3 - x) * (6 - x) * (3 - y) * (6 - y)) :=
    div_pos hpolyA hden_pos
  have hquotB :
      0 < (2 * x + 2 * y - x * y) /
        ((3 - x) * (6 - x) * (3 - y) * (6 - y)) :=
    div_pos hpolyB hden_pos
  have hdiffA :
      schurLevelOneDiagonal x - schurLevelOneDiagonal y =
        (y - x) *
          (1 + 2 * ((18 - 4 * x - 4 * y + x * y) /
            ((3 - x) * (6 - x) * (3 - y) * (6 - y)))) := by
    unfold schurLevelOneDiagonal
    field_simp [ne_of_gt hx3, ne_of_gt hx6,
      ne_of_gt hy3, ne_of_gt hy6]
    <;> ring
  have hdiffB :
      schurLevelOneOffDiagonal y -
        schurLevelOneOffDiagonal x =
        (y - x) *
          ((2 * x + 2 * y - x * y) /
            ((3 - x) * (6 - x) * (3 - y) * (6 - y))) := by
    unfold schurLevelOneOffDiagonal
    field_simp [ne_of_gt hx3, ne_of_gt hx6,
      ne_of_gt hy3, ne_of_gt hy6]
    <;> ring
  constructor
  · have hfactor :
        0 ≤ 1 + 2 * ((18 - 4 * x - 4 * y + x * y) /
          ((3 - x) * (6 - x) * (3 - y) * (6 - y))) :=
      le_of_lt (by linarith)
    rw [← sub_nonneg]
    rw [hdiffA]
    exact mul_nonneg (sub_nonneg.mpr hxy) hfactor
  · rw [← sub_nonneg]
    rw [hdiffB]
    exact mul_nonneg (sub_nonneg.mpr hxy) (le_of_lt hquotB)


/-- Exact rational enclosure of the first Schur state on the full narrow
bootstrap interval. This keeps the dependence between the initial
diagonal value and lambda instead of treating them as independent. -/
theorem schurBootstrap_levelOne_state_box
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper) :
    ((1235695422588800493636603471580679174544749349869 /
        10 ^ 50 : ℝ) ≤
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).1 ∧
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).1 ≤
        (1235695422588800493636603471580679433299227360878 /
          10 ^ 50 : ℝ)) ∧
    (-(8710298126456400450881962728061450813934618792872 /
        10 ^ 50 : ℝ) ≤
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).2 ∧
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).2 ≤
        -(8710298126456400450881962728061450802735668500291 /
          10 ^ 50 : ℝ)) := by
  have hle :
      schurBootstrapLambdaLower ≤ schurBootstrapLambdaUpper := by
    norm_num [schurBootstrapLambdaLower, schurBootstrapLambdaUpper]
  have hL :
      schurBootstrapLambdaLower ∈
        Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper :=
    ⟨le_rfl, hle⟩
  have hU :
      schurBootstrapLambdaUpper ∈
        Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper :=
    ⟨hle, le_rfl⟩
  have hlow :=
    schurBootstrap_levelOne_antitone_mono
      schurBootstrapLambdaLower lambda hL hlambda hlambda.1
  have hupp :=
    schurBootstrap_levelOne_antitone_mono
      lambda schurBootstrapLambdaUpper hlambda hU hlambda.2
  have hA_lower :
      (1235695422588800493636603471580679174544749349869 /
        10 ^ 50 : ℝ) ≤
        schurLevelOneDiagonal schurBootstrapLambdaUpper := by
    norm_num [schurLevelOneDiagonal, schurBootstrapLambdaUpper]
  have hA_upper :
      schurLevelOneDiagonal schurBootstrapLambdaLower ≤
        (1235695422588800493636603471580679433299227360878 /
          10 ^ 50 : ℝ) := by
    norm_num [schurLevelOneDiagonal, schurBootstrapLambdaLower]
  have hB_lower :
      -(8710298126456400450881962728061450813934618792872 /
        10 ^ 50 : ℝ) ≤
        schurLevelOneOffDiagonal schurBootstrapLambdaLower := by
    norm_num [schurLevelOneOffDiagonal, schurBootstrapLambdaLower]
  have hB_upper :
      schurLevelOneOffDiagonal schurBootstrapLambdaUpper ≤
        -(8710298126456400450881962728061450802735668500291 /
          10 ^ 50 : ℝ) := by
    norm_num [schurLevelOneOffDiagonal, schurBootstrapLambdaUpper]
  rw [schurBoundaryTrajectory_level_one_formula]
  exact
    ⟨⟨le_trans hA_lower hupp.1,
        le_trans hlow.1 hA_upper⟩,
      ⟨le_trans hB_lower hlow.2,
        le_trans hupp.2 hB_upper⟩⟩



/-- Uniform coarse enclosure of the level-two Schur state over the full
narrow parameter interval. The first-level interval is propagated using
rational numerator/denominator bounds, keeping every division denominator
strictly positive. -/
theorem schurBootstrap_levelTwo_state_box
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper) :
    |(schurBoundaryTrajectory lambda (2 - lambda, 1) 2).1| ≤
        (1 / 1000 : ℝ) ∧
      -(7 / 1000 : ℝ) ≤
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).2 ∧
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).2 ≤ 0 := by
  let a1 : ℝ :=
    (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).1
  let b1 : ℝ :=
    (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).2
  let c1 : ℝ := schurMidpointPivot a1 b1 lambda
  let c13 : ℝ := c1 + 3 * b1
  let rA : ℝ := (c1 + b1) / (c1 * c13)
  let rB : ℝ := (c1 - b1) / (c1 * c13)
  let a2 : ℝ := (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).1
  let b2 : ℝ := (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).2
  have hparam_lower : (130912 / 100000 : ℝ) ≤ lambda := by
    calc
      (130912 / 100000 : ℝ) ≤ schurBootstrapLambdaLower := by
        norm_num [schurBootstrapLambdaLower]
      _ ≤ lambda := hlambda.1
  have hparam_upper : lambda ≤ (130914 / 100000 : ℝ) := by
    calc
      lambda ≤ schurBootstrapLambdaUpper := hlambda.2
      _ ≤ (130914 / 100000 : ℝ) := by
        norm_num [schurBootstrapLambdaUpper]
  have hlevelOne := schurBootstrap_levelOne_state_box lambda hlambda
  have ha1_lower : (123569 / 10 ^ 7 : ℝ) ≤ a1 := by
    have hExact :
        (1235695422588800493636603471580679174544749349869 /
          10 ^ 50 : ℝ) ≤ a1 := by
      simpa [a1] using hlevelOne.1.1
    exact le_trans (by norm_num) hExact
  have ha1_upper : a1 ≤ (123570 / 10 ^ 7 : ℝ) := by
    have hExact :
        a1 ≤
          (1235695422588800493636603471580679433299227360878 /
            10 ^ 50 : ℝ) := by
      simpa [a1] using hlevelOne.1.2
    exact le_trans hExact (by norm_num)
  have hb1_lower : -(871030 / 10 ^ 7 : ℝ) ≤ b1 := by
    have hExact :
        -(8710298126456400450881962728061450813934618792872 /
          10 ^ 50 : ℝ) ≤ b1 := by
      simpa [b1] using hlevelOne.2.1
    exact le_trans (by norm_num) hExact
  have hb1_upper : b1 ≤ -(871029 / 10 ^ 7 : ℝ) := by
    have hExact :
        b1 ≤
          -(8710298126456400450881962728061450802735668500291 /
            10 ^ 50 : ℝ) := by
      simpa [b1] using hlevelOne.2.2
    exact le_trans hExact (by norm_num)
  have hc1_lower : (142093 / 100000 : ℝ) ≤ c1 := by
    dsimp [c1, schurMidpointPivot]
    nlinarith
  have hc1_upper : c1 ≤ (142096 / 100000 : ℝ) := by
    dsimp [c1, schurMidpointPivot]
    nlinarith
  have hc13_lower : (115962 / 100000 : ℝ) ≤ c13 := by
    dsimp [c13]
    linarith
  have hc13_upper : c13 ≤ (115966 / 100000 : ℝ) := by
    dsimp [c13]
    linarith
  have hc_pos : 0 < c1 := by linarith
  have hc13_pos : 0 < c13 := by linarith
  have hden_pos : 0 < c1 * c13 := mul_pos hc_pos hc13_pos
  have hc1_coarse_lower : (142 / 100 : ℝ) ≤ c1 := by linarith
  have hc1_coarse_upper : c1 ≤ (1422 / 1000 : ℝ) := by linarith
  have hc13_coarse_lower : (1159 / 1000 : ℝ) ≤ c13 := by linarith
  have hc13_coarse_upper : c13 ≤ (1161 / 1000 : ℝ) := by linarith
  have hden_lower : (1647 / 1000 : ℝ) ≤ c1 * c13 := by
    calc
      (1647 / 1000 : ℝ) ≤
          (142093 / 100000 : ℝ) * (115962 / 100000 : ℝ) := by
        norm_num
      _ ≤ c1 * (115962 / 100000 : ℝ) :=
        mul_le_mul_of_nonneg_right hc1_lower (by norm_num)
      _ ≤ c1 * c13 :=
        mul_le_mul_of_nonneg_left hc13_lower (le_of_lt hc_pos)
  have hden_upper : c1 * c13 ≤ (1649 / 1000 : ℝ) := by
    calc
      c1 * c13 ≤
          (142096 / 100000 : ℝ) * (115966 / 100000 : ℝ) :=
        mul_le_mul hc1_upper hc13_upper (le_of_lt hc13_pos) (by norm_num)
      _ ≤ (1649 / 1000 : ℝ) := by norm_num
  have hnumA_lower : (1333 / 1000 : ℝ) ≤ c1 + b1 := by
    dsimp [c1]
    linarith
  have hnumA_upper : c1 + b1 ≤ (1335 / 1000 : ℝ) := by
    dsimp [c1]
    linarith
  have hnumB_lower : (1508 / 1000 : ℝ) ≤ c1 - b1 := by
    dsimp [c1]
    linarith
  have hnumB_upper : c1 - b1 ≤ (1509 / 1000 : ℝ) := by
    dsimp [c1]
    linarith
  have hrA_lower : (4 / 5 : ℝ) ≤ rA := by
    dsimp [rA]
    apply (le_div_iff₀ hden_pos).2
    calc
      (4 / 5 : ℝ) * (c1 * c13)
          ≤ (4 / 5 : ℝ) * (1649 / 1000 : ℝ) :=
            mul_le_mul_of_nonneg_left hden_upper (by norm_num)
      _ ≤ (1333 / 1000 : ℝ) := by norm_num
      _ ≤ c1 + b1 := hnumA_lower
  have hrA_upper : rA ≤ (82 / 100 : ℝ) := by
    dsimp [rA]
    apply (div_le_iff₀ hden_pos).2
    calc
      c1 + b1 ≤ (1335 / 1000 : ℝ) := hnumA_upper
      _ ≤ (82 / 100 : ℝ) * (1647 / 1000 : ℝ) := by norm_num
      _ ≤ (82 / 100 : ℝ) * (c1 * c13) :=
        mul_le_mul_of_nonneg_left hden_lower (by norm_num)
  have hrB_lower : (91 / 100 : ℝ) ≤ rB := by
    dsimp [rB]
    apply (le_div_iff₀ hden_pos).2
    calc
      (91 / 100 : ℝ) * (c1 * c13)
          ≤ (91 / 100 : ℝ) * (1649 / 1000 : ℝ) :=
            mul_le_mul_of_nonneg_left hden_upper (by norm_num)
      _ ≤ (1508 / 1000 : ℝ) := by norm_num
      _ ≤ c1 - b1 := hnumB_lower
  have hrB_upper : rB ≤ (92 / 100 : ℝ) := by
    dsimp [rB]
    apply (div_le_iff₀ hden_pos).2
    calc
      c1 - b1 ≤ (1509 / 1000 : ℝ) := hnumB_upper
      _ ≤ (92 / 100 : ℝ) * (1647 / 1000 : ℝ) := by norm_num
      _ ≤ (92 / 100 : ℝ) * (c1 * c13) :=
        mul_le_mul_of_nonneg_left hden_lower (by norm_num)
  have hb1_mag_lower : (871 / 10000 : ℝ) ≤ -b1 := by
    dsimp [b1]
    linarith
  have hb1_mag_upper : -b1 ≤ (8711 / 100000 : ℝ) := by
    dsimp [b1]
    linarith
  have hb1_sq_lower : (3 / 400 : ℝ) ≤ b1 ^ 2 := by
    have hcross := mul_nonneg
      (sub_nonneg.mpr hb1_mag_lower)
      (by linarith : 0 ≤ -b1 + (871 / 10000 : ℝ))
    nlinarith [hcross]
  have hb1_sq_upper : b1 ^ 2 ≤ (76 / 10000 : ℝ) := by
    have hcross := mul_nonneg
      (sub_nonneg.mpr hb1_mag_upper)
      (by linarith : 0 ≤ -b1 + (8711 / 100000 : ℝ))
    nlinarith [hcross]
  have hprodA_lower :
      (3 / 400 : ℝ) * (4 / 5 : ℝ) ≤ b1 ^ 2 * rA := by
    calc
      (3 / 400 : ℝ) * (4 / 5 : ℝ)
          ≤ b1 ^ 2 * (4 / 5 : ℝ) :=
            mul_le_mul_of_nonneg_right hb1_sq_lower (by norm_num)
      _ ≤ b1 ^ 2 * rA :=
        mul_le_mul_of_nonneg_left hrA_lower (sq_nonneg b1)
  have hprodA_upper :
      b1 ^ 2 * rA ≤
        (76 / 10000 : ℝ) * (82 / 100 : ℝ) := by
    calc
      b1 ^ 2 * rA ≤ b1 ^ 2 * (82 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hrA_upper (sq_nonneg b1)
      _ ≤ (76 / 10000 : ℝ) * (82 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hb1_sq_upper (by norm_num)
  have hqA_lower :
      (12 / 1000 : ℝ) ≤ 2 * b1 ^ 2 * rA := by
    nlinarith [hprodA_lower]
  have hqA_upper :
      2 * b1 ^ 2 * rA ≤ (12464 / 10 ^ 6 : ℝ) := by
    nlinarith [hprodA_upper]
  have ha2_step :
      a2 = schurNextDiagonal a1 b1 c1 := by
    dsimp [a2, a1, b1, c1]
    rfl
  have ha2_change : a2 - a1 = -(2 * b1 ^ 2 * rA) := by
    have h := schurNextDiagonal_sub_eq a1 b1 c1
    rw [← ha2_step] at h
    simpa [rA] using h
  have ha2_lower : -(1 / 1000 : ℝ) ≤ a2 := by
    linarith [ha1_lower, hqA_upper, ha2_change]
  have ha2_upper : a2 ≤ (1 / 1000 : ℝ) := by
    linarith [ha1_upper, hqA_lower, ha2_change]
  have hb2_step :
      b2 = schurNextOffDiagonal b1 c1 := by
    dsimp [b2, a1, b1, c1]
    rfl
  have hb2_formula : -b2 = b1 ^ 2 * rB := by
    rw [hb2_step]
    unfold schurNextOffDiagonal
    dsimp [rB]
    ring
  have hprodB_upper :
      b1 ^ 2 * rB ≤
        (76 / 10000 : ℝ) * (92 / 100 : ℝ) := by
    calc
      b1 ^ 2 * rB ≤ b1 ^ 2 * (92 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hrB_upper (sq_nonneg b1)
      _ ≤ (76 / 10000 : ℝ) * (92 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hb1_sq_upper (by norm_num)
  have hb2_upper : b2 ≤ 0 := by
    rw [← neg_nonneg]
    rw [hb2_formula]
    exact mul_nonneg (sq_nonneg b1) (le_of_lt (by linarith [hrB_lower]))
  have hb2_lower : -(7 / 1000 : ℝ) ≤ b2 := by
    have hnum : b1 ^ 2 * rB ≤ (7 / 1000 : ℝ) := by
      calc
        b1 ^ 2 * rB ≤
            (76 / 10000 : ℝ) * (92 / 100 : ℝ) :=
          hprodB_upper
        _ ≤ (7 / 1000 : ℝ) := by norm_num
    calc
      -(7 / 1000 : ℝ) ≤ -(b1 ^ 2 * rB) := neg_le_neg hnum
      _ = b2 := by linarith [hb2_formula]
  exact ⟨abs_le.mpr ⟨ha2_lower, ha2_upper⟩,
    hb2_lower, hb2_upper⟩

/-- Uniform level-three enclosure over the narrow bootstrap parameter
interval. The level-two coarse box has positive Schur denominators; one
more exact Schur step contracts the off-diagonal coordinate below
1/20000 and keeps the diagonal coordinate below 1/500. -/
theorem schurBootstrap_levelThree_state_box
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper) :
    |(schurBoundaryTrajectory lambda (2 - lambda, 1) 3).1| ≤
        (1 / 500 : ℝ) ∧
      -(1 / 20000 : ℝ) ≤
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 3).2 ∧
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 3).2 ≤ 0 := by
  let a2 : ℝ :=
    (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).1
  let b2 : ℝ :=
    (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).2
  let c2 : ℝ := schurMidpointPivot a2 b2 lambda
  let c23 : ℝ := c2 + 3 * b2
  let rA : ℝ := (c2 + b2) / (c2 * c23)
  let rB : ℝ := (c2 - b2) / (c2 * c23)
  let a3 : ℝ :=
    (schurBoundaryTrajectory lambda (2 - lambda, 1) 3).1
  let b3 : ℝ :=
    (schurBoundaryTrajectory lambda (2 - lambda, 1) 3).2
  have hwindow := schurBootstrapEndpoints_in_parameter_window
  have hlambda_lower : (1309 / 1000 : ℝ) ≤ lambda :=
    le_trans hwindow.1 hlambda.1
  have hlambda_upper : lambda ≤ (131 / 100 : ℝ) :=
    le_trans hlambda.2 hwindow.2.2.2
  have hlevelTwo :=
    schurBootstrap_levelTwo_state_box lambda hlambda
  have ha2_lower : -(1 / 1000 : ℝ) ≤ a2 := by
    have h := (abs_le.mp hlevelTwo.1).1
    simpa [a2] using h
  have ha2_upper : a2 ≤ (1 / 1000 : ℝ) := by
    have h := (abs_le.mp hlevelTwo.1).2
    simpa [a2] using h
  have hb2_lower : -(7 / 1000 : ℝ) ≤ b2 := by
    simpa [b2] using hlevelTwo.2.1
  have hb2_upper : b2 ≤ 0 := by
    simpa [b2] using hlevelTwo.2.2
  have hc2_lower : (1307 / 1000 : ℝ) ≤ c2 := by
    dsimp [c2, schurMidpointPivot]
    nlinarith [ha2_lower, hb2_upper, hlambda_lower]
  have hc2_upper : c2 ≤ (132 / 100 : ℝ) := by
    dsimp [c2, schurMidpointPivot]
    nlinarith [ha2_upper, hb2_lower, hlambda_upper]
  have hc23_lower : (1293 / 1000 : ℝ) ≤ c23 := by
    dsimp [c23, c2, schurMidpointPivot]
    nlinarith [ha2_lower, hb2_lower, hlambda_lower]
  have hc_pos : 0 < c2 := by linarith
  have hc23_pos : 0 < c23 := by linarith
  have hden_pos : 0 < c2 * c23 := mul_pos hc_pos hc23_pos
  have hnumA_pos : 0 < c2 + b2 := by
    linarith [hc2_lower, hb2_lower]
  have hrA_lower : 0 ≤ rA := by
    dsimp [rA]
    exact le_of_lt (div_pos hnumA_pos hden_pos)
  have hc23_one : (1 : ℝ) ≤ c23 := by linarith
  have hden_c_lower : c2 ≤ c2 * c23 := by
    calc
      c2 = c2 * 1 := by ring
      _ ≤ c2 * c23 :=
        mul_le_mul_of_nonneg_left hc23_one (le_of_lt hc_pos)
  have hnumA_upper : c2 + b2 ≤ c2 := by linarith
  have hrA_upper : rA ≤ 1 := by
    dsimp [rA]
    apply (div_le_iff₀ hden_pos).2
    calc
      c2 + b2 ≤ c2 := hnumA_upper
      _ ≤ c2 * c23 := hden_c_lower
      _ = 1 * (c2 * c23) := by ring
  have hnumB_pos : 0 < c2 - b2 := by linarith
  have hrB_lower : 0 ≤ rB := by
    dsimp [rB]
    exact le_of_lt (div_pos hnumB_pos hden_pos)
  have hnumB_upper : c2 - b2 ≤ (1326 / 1000 : ℝ) := by
    dsimp [c2, schurMidpointPivot]
    nlinarith [ha2_upper, hb2_lower, hlambda_upper]
  have hdenB_lower : (1326 / 1000 : ℝ) ≤ c2 * c23 := by
    calc
      (1326 / 1000 : ℝ) ≤
          (1307 / 1000 : ℝ) * (1293 / 1000 : ℝ) := by norm_num
      _ ≤ c2 * (1293 / 1000 : ℝ) :=
        mul_le_mul_of_nonneg_right hc2_lower (by norm_num)
      _ ≤ c2 * c23 :=
        mul_le_mul_of_nonneg_left hc23_lower (le_of_lt hc_pos)
  have hrB_upper : rB ≤ 1 := by
    dsimp [rB]
    apply (div_le_iff₀ hden_pos).2
    calc
      c2 - b2 ≤ (1326 / 1000 : ℝ) := hnumB_upper
      _ ≤ c2 * c23 := hdenB_lower
      _ = 1 * (c2 * c23) := by ring
  have ha3_step :
      a3 = schurNextDiagonal a2 b2 c2 := by
    dsimp [a3, a2, b2, c2]
    rfl
  have hb3_step :
      b3 = schurNextOffDiagonal b2 c2 := by
    dsimp [b3, a2, b2, c2]
    rfl
  have ha3_change : a3 - a2 = -(2 * b2 ^ 2 * rA) := by
    have h := schurNextDiagonal_sub_eq a2 b2 c2
    rw [← ha3_step] at h
    simpa [rA] using h
  have hb3_formula : -b3 = b2 ^ 2 * rB := by
    rw [hb3_step]
    unfold schurNextOffDiagonal
    dsimp [rB]
    ring
  have hb2_mag_nonneg : 0 ≤ -b2 := by linarith
  have hb2_mag_upper : -b2 ≤ (7 / 1000 : ℝ) := by linarith
  have hb2_sq_upper : b2 ^ 2 ≤ (49 / 10 ^ 6 : ℝ) := by
    have hmul₁ :
        (-b2) * (-b2) ≤ (7 / 1000 : ℝ) * (-b2) :=
      mul_le_mul_of_nonneg_right hb2_mag_upper hb2_mag_nonneg
    have hmul₂ :
        (7 / 1000 : ℝ) * (-b2) ≤
          (7 / 1000 : ℝ) * (7 / 1000 : ℝ) :=
      mul_le_mul_of_nonneg_left hb2_mag_upper (by norm_num)
    nlinarith [hmul₁, hmul₂]
  have hchange_upper : a3 - a2 ≤ 0 := by
    rw [ha3_change]
    have hprod : 0 ≤ 2 * b2 ^ 2 * rA :=
      mul_nonneg (by positivity) hrA_lower
    linarith
  have hchange_lower : -(2 * b2 ^ 2) ≤ a3 - a2 := by
    rw [ha3_change]
    have hcoeff : 0 ≤ (2 * b2 ^ 2 : ℝ) := by positivity
    have hprod :
        2 * b2 ^ 2 * rA ≤ 2 * b2 ^ 2 := by
      calc
        (2 * b2 ^ 2) * rA ≤ (2 * b2 ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hrA_upper hcoeff
        _ = 2 * b2 ^ 2 := by ring
    linarith
  have ha3_lower : -(1 / 500 : ℝ) ≤ a3 := by
    nlinarith [ha2_lower, hb2_sq_upper, hchange_lower]
  have ha3_upper : a3 ≤ (1 / 500 : ℝ) := by
    linarith [ha2_upper, hchange_upper]
  have hprodB_upper :
      b2 ^ 2 * rB ≤ (1 / 20000 : ℝ) := by
    calc
      b2 ^ 2 * rB ≤ b2 ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hrB_upper (sq_nonneg b2)
      _ = b2 ^ 2 := by ring
      _ ≤ (49 / 10 ^ 6 : ℝ) := hb2_sq_upper
      _ ≤ (1 / 20000 : ℝ) := by norm_num
  have hb3_lower : -(1 / 20000 : ℝ) ≤ b3 := by
    calc
      -(1 / 20000 : ℝ) ≤ -(b2 ^ 2 * rB) :=
        neg_le_neg hprodB_upper
      _ = b3 := by linarith [hb3_formula]
  have hb3_upper : b3 ≤ 0 := by
    rw [← neg_nonneg]
    rw [hb3_formula]
    exact mul_nonneg (sq_nonneg b2) hrB_lower
  exact ⟨abs_le.mpr ⟨ha3_lower, ha3_upper⟩,
    hb3_lower, hb3_upper⟩



/-- The first three Schur pivot pairs are strictly positive throughout the
bootstrap parameter interval. The level-one and level-two rational enclosures
supply the only nontrivial finite-prefix estimates. -/
theorem schurBootstrap_firstThree_pivots_nonzero :
    ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper →
      ∀ k, k < 3 →
        schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda ≠ 0 ∧
        schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda +
          3 * (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2 ≠ 0 := by
  intro lambda hlambda k hk
  have hwindow := schurBootstrapEndpoints_in_parameter_window
  have hlambda_lower :
      (1309 / 1000 : ℝ) ≤ lambda :=
    le_trans hwindow.1 hlambda.1
  have hlambda_upper :
      lambda ≤ (131 / 100 : ℝ) :=
    le_trans hlambda.2 hwindow.2.2.2
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · have hc0_pos :
        0 < schurMidpointPivot (2 - lambda) 1 lambda := by
      unfold schurMidpointPivot
      nlinarith [hlambda_upper]
    have hc03_pos :
        0 < schurMidpointPivot (2 - lambda) 1 lambda + 3 * (1 : ℝ) := by
      unfold schurMidpointPivot
      nlinarith [hlambda_upper]
    change
      schurMidpointPivot (2 - lambda) 1 lambda ≠ 0 ∧
        schurMidpointPivot (2 - lambda) 1 lambda +
          3 * (1 : ℝ) ≠ 0
    exact ⟨ne_of_gt hc0_pos, ne_of_gt hc03_pos⟩
  · let a1 : ℝ :=
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).1
    let b1 : ℝ :=
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 1).2
    have hlevelOne := schurBootstrap_levelOne_state_box lambda hlambda
    have ha1_exact :
        (1235695422588800493636603471580679174544749349869 /
          10 ^ 50 : ℝ) ≤ a1 := by
      simpa [a1] using hlevelOne.1.1
    have ha1_lower : (1 / 100 : ℝ) ≤ a1 := by
      have hcoarse :
          (1 / 100 : ℝ) ≤
            (1235695422588800493636603471580679174544749349869 /
              10 ^ 50 : ℝ) := by norm_num
      exact le_trans hcoarse ha1_exact
    have hb1_exact_lower :
        -(8710298126456400450881962728061450813934618792872 /
          10 ^ 50 : ℝ) ≤ b1 := by
      simpa [b1] using hlevelOne.2.1
    have hb1_lower : -(9 / 100 : ℝ) ≤ b1 := by
      have hcoarse :
          -(9 / 100 : ℝ) ≤
            -(8710298126456400450881962728061450813934618792872 /
              10 ^ 50 : ℝ) := by norm_num
      exact le_trans hcoarse hb1_exact_lower
    have hb1_exact_upper :
        b1 ≤ -(8710298126456400450881962728061450802735668500291 /
          10 ^ 50 : ℝ) := by
      simpa [b1] using hlevelOne.2.2
    have hb1_upper : b1 ≤ 0 := by
      have hnegative :
          -(8710298126456400450881962728061450802735668500291 /
            10 ^ 50 : ℝ) ≤ 0 := by norm_num
      exact le_trans hb1_exact_upper hnegative
    have hc1_pos :
        0 < schurMidpointPivot a1 b1 lambda := by
      unfold schurMidpointPivot
      nlinarith [ha1_lower, hb1_upper, hlambda_lower]
    have hc13_pos :
        0 < schurMidpointPivot a1 b1 lambda + 3 * b1 := by
      unfold schurMidpointPivot
      nlinarith [ha1_lower, hb1_lower, hlambda_lower]
    change
      schurMidpointPivot a1 b1 lambda ≠ 0 ∧
        schurMidpointPivot a1 b1 lambda + 3 * b1 ≠ 0
    exact ⟨ne_of_gt hc1_pos, ne_of_gt hc13_pos⟩
  · let a2 : ℝ :=
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).1
    let b2 : ℝ :=
      (schurBoundaryTrajectory lambda (2 - lambda, 1) 2).2
    have hlevelTwo := schurBootstrap_levelTwo_state_box lambda hlambda
    have ha2_lower : -(1 / 1000 : ℝ) ≤ a2 := by
      have h := (abs_le.mp hlevelTwo.1).1
      simpa [a2] using h
    have hb2_lower : -(7 / 1000 : ℝ) ≤ b2 := by
      simpa [b2] using hlevelTwo.2.1
    have hb2_upper : b2 ≤ 0 := by
      simpa [b2] using hlevelTwo.2.2
    have hc2_pos :
        0 < schurMidpointPivot a2 b2 lambda := by
      unfold schurMidpointPivot
      nlinarith [ha2_lower, hb2_upper, hlambda_lower]
    have hc23_pos :
        0 < schurMidpointPivot a2 b2 lambda + 3 * b2 := by
      unfold schurMidpointPivot
      nlinarith [ha2_lower, hb2_lower, hlambda_lower]
    change
      schurMidpointPivot a2 b2 lambda ≠ 0 ∧
        schurMidpointPivot a2 b2 lambda + 3 * b2 ≠ 0
    exact ⟨ne_of_gt hc2_pos, ne_of_gt hc23_pos⟩


/-- The level-three state enclosure and the coarse trajectory invariant make
every later Schur pivot pair positive. Together with the explicit three-step
prefix, all denominator checks for the bootstrap interval are discharged. -/
theorem schurBootstrap_all_pivots_nonzero :
    ∀ lambda, lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper →
      ∀ k,
        schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda ≠ 0 ∧
        schurMidpointPivot
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).1
            (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2
            lambda +
          3 * (schurBoundaryTrajectory lambda (2 - lambda, 1) k).2 ≠ 0 := by
  intro lambda hlambda k
  by_cases hk : k < 3
  · exact schurBootstrap_firstThree_pivots_nonzero lambda hlambda k hk
  · have hkge : 3 ≤ k := by omega
    obtain ⟨m, hm⟩ : ∃ m, k = 3 + m := by
      refine ⟨k - 3, ?_⟩
      omega
    subst k
    have hwindow := schurBootstrapEndpoints_in_parameter_window
    have hlambda_lower :
        (1309 / 1000 : ℝ) ≤ lambda :=
      le_trans hwindow.1 hlambda.1
    have hlambda_upper :
        lambda ≤ (131 / 100 : ℝ) :=
      le_trans hlambda.2 hwindow.2.2.2
    have hstart := schurBootstrap_levelThree_state_box lambda hlambda
    have hstate :=
      schurBoundaryTrajectory_coarse_state_box lambda
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 3).1
        (schurBoundaryTrajectory lambda (2 - lambda, 1) 3).2
        hstart.1 hstart.2.1 hstart.2.2
        hlambda_lower hlambda_upper m
    rw [schurBoundaryTrajectory_add lambda (2 - lambda, 1) 3 m]
    have ha_lower := (abs_le.mp hstate.1).1
    have hc_lower :
        (13 / 10 : ℝ) ≤
          schurMidpointPivot
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).1
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).2
            lambda := by
      unfold schurMidpointPivot
      nlinarith [ha_lower, hstate.2.2, hlambda_lower]
    have hc3_lower :
        (13 / 10 : ℝ) ≤
          schurMidpointPivot
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).1
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).2
              lambda +
            3 * (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).2 := by
      unfold schurMidpointPivot
      nlinarith [ha_lower, hstate.2.1, hlambda_lower]
    have hc_pos :
        0 <
          schurMidpointPivot
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).1
            (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).2
            lambda :=
      lt_of_lt_of_le (by norm_num) hc_lower
    have hc3_pos :
        0 <
          schurMidpointPivot
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).1
              (schurBoundaryTrajectory lambda
                (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).2
              lambda +
            3 * (schurBoundaryTrajectory lambda
              (schurBoundaryTrajectory lambda (2 - lambda, 1) 3) m).2 :=
      lt_of_lt_of_le (by norm_num) hc3_lower
    exact ⟨ne_of_gt hc_pos, ne_of_gt hc3_pos⟩


/-- Every finite-level bootstrap A1 characteristic has a zero in the
parameter interval: the three initial pivot pairs are positive explicitly,
and the level-three invariant makes all later denominators positive. -/
theorem schurBootstrapA1AtLevel_exists_root (n : ℕ) :
    ∃ lambda ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper,
      schurBootstrapA1AtLevel lambda n = 0 := by
  apply schurBootstrapA1AtLevel_exists_root_of_nonzero_pivots n
  intro lambda hlambda k hk
  exact schurBootstrap_all_pivots_nonzero lambda hlambda k

/-- Uniform finite-tail estimate, obtained by shifting the level-three
trajectory and summing the half-contracting off-diagonal coefficients. -/
theorem schurBootstrapA1AtLevel_tail_bound
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper) :
    ∀ m N,
      0 ≤ schurBootstrapA1AtLevel lambda (m + N) -
        schurBootstrapA1AtLevel lambda m ∧
      schurBootstrapA1AtLevel lambda (m + N) -
        schurBootstrapA1AtLevel lambda m ≤
          (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ m := by
  have hwindow := schurBootstrapEndpoints_in_parameter_window
  have hlambdaLower : (1309 / 1000 : ℝ) ≤ lambda := le_trans hwindow.1 hlambda.1
  have hlambdaUpper : lambda ≤ (131 / 100 : ℝ) := le_trans hlambda.2 hwindow.2.2.2
  let initial : ℝ × ℝ := (2 - lambda, 1)
  let s3 := schurBoundaryTrajectory lambda initial 3
  have hs3 := schurBootstrap_levelThree_state_box lambda hlambda
  have hs3' : |s3.1| ≤ (1 / 500 : ℝ) ∧
      -(1 / 20000 : ℝ) ≤ s3.2 ∧ s3.2 ≤ 0 := by
    simpa [s3, initial] using hs3
  have hbabs : |s3.2| ≤ (1 / 20000 : ℝ) := by
    apply abs_le.mpr
    exact ⟨hs3'.2.1, le_trans hs3'.2.2 (by norm_num)⟩
  have hcontract :=
    schurBoundaryTrajectory_coarse_offDiagonal_half_contract
      lambda s3.1 s3.2 hs3'.1 hs3'.2.1 hs3'.2.2 hlambdaLower hlambdaUpper
  have hinc :=
    schurBoundaryTrajectory_coarse_A1_increment_bounds
      lambda s3.1 s3.2 hs3'.1 hs3'.2.1 hs3'.2.2 hlambdaLower hlambdaUpper
  intro m N
  let f : ℕ → ℝ := fun k =>
    (schurBoundaryTrajectory lambda s3 (3 + m + k)).1 +
      2 * (schurBoundaryTrajectory lambda s3 (3 + m + k)).2
  let u : ℕ → ℝ :=
    fun k => |(schurBoundaryTrajectory lambda s3 (3 + m + k)).2|
  have hu0 : u 0 ≤ (1 / 160000 : ℝ) * (1 / 2 : ℝ) ^ m := by
    change |(schurBoundaryTrajectory lambda s3 (3 + m)).2| ≤ _
    have hdecay : ∀ n,
        |(schurBoundaryTrajectory lambda s3 n).2| ≤
          |s3.2| * (1 / 2 : ℝ) ^ n := by
      intro n
      induction n with
      | zero => simp [schurBoundaryTrajectory]
      | succ n ih =>
          calc
            |(schurBoundaryTrajectory lambda s3 (n + 1)).2|
                ≤ (1 / 2 : ℝ) *
                    |(schurBoundaryTrajectory lambda s3 n).2| := hcontract n
            _ ≤ (1 / 2 : ℝ) * (|s3.2| * (1 / 2 : ℝ)^n) :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
            _ = |s3.2| * (1 / 2 : ℝ)^(n+1) := by rw [pow_succ]; ring
    calc
      |(schurBoundaryTrajectory lambda s3 (3 + m)).2|
          ≤ |s3.2| * (1 / 2 : ℝ)^(3 + m) := hdecay (3 + m)
      _ ≤ (1 / 20000 : ℝ) * (1 / 2 : ℝ)^(3 + m) :=
        mul_le_mul_of_nonneg_right hbabs (by positivity)
      _ = (1 / 160000 : ℝ) * (1 / 2 : ℝ)^m := by rw [pow_add]; ring
  have hu_nonneg : ∀ k, 0 ≤ u k := fun k => abs_nonneg _
  have hucontract : ∀ k, u (k+1) ≤ (1/2 : ℝ) * u k := by
    intro k
    simpa [u, Nat.add_assoc] using hcontract (3 + m + k)
  have hsumu :=
    sum_range_le_two_mul_initial_of_half_contraction u N hu_nonneg hucontract
  have hsuminc0 : 0 ≤ ∑ k ∈ Finset.range N, (f (k+1)-f k) := by
    apply Finset.sum_nonneg
    intro k hk
    simpa [f, Nat.add_assoc] using (hinc (3 + m + k)).1
  have hsuminc1 :
      (∑ k ∈ Finset.range N, (f (k+1)-f k)) ≤
        2 * (∑ k ∈ Finset.range N, u k) := by
    calc
      (∑ k ∈ Finset.range N, (f (k+1)-f k))
          ≤ ∑ k ∈ Finset.range N, 2*u k := by
            apply Finset.sum_le_sum
            intro k hk
            simpa [f,u,Nat.add_assoc] using (hinc (3 + m + k)).2
      _ = 2 * (∑ k ∈ Finset.range N, u k) := by rw [← Finset.mul_sum]
  have htel := sum_range_step_difference_eq f N
  have hlower : 0 ≤ f N - f 0 := by rw [← htel]; exact hsuminc0
  have hupper : f N - f 0 ≤ 4*u 0 := by
    rw [← htel]
    calc
      (∑ k ∈ Finset.range N, (f (k+1)-f k))
          ≤ 2 * (∑ k ∈ Finset.range N, u k) := hsuminc1
      _ ≤ 2 * (2*u 0) := mul_le_mul_of_nonneg_left hsumu (by norm_num)
      _ = 4*u 0 := by ring
  have hsmall : 4*u 0 ≤ (1/40000 : ℝ)*(1/2 : ℝ)^m := by
    calc
      4*u 0 ≤ 4*((1/160000 : ℝ)*(1/2 : ℝ)^m) :=
        mul_le_mul_of_nonneg_left hu0 (by norm_num)
      _ = (1/40000 : ℝ)*(1/2 : ℝ)^m := by ring
  have hA (k : ℕ) :
      schurBootstrapA1AtLevel lambda k =
        (schurBoundaryTrajectory lambda s3 (3+k)).1 +
          2*(schurBoundaryTrajectory lambda s3 (3+k)).2 := by
    unfold schurBootstrapA1AtLevel
    have hk : 6+k = 3+(3+k) := by omega
    rw [hk, schurBoundaryTrajectory_add lambda initial 3 (3+k)]
  have hstart : schurBootstrapA1AtLevel lambda m = f 0 := by rw [hA]; simp [f]
  have hend : schurBootstrapA1AtLevel lambda (m+N) = f N := by
    rw [hA]; simp [f, Nat.add_assoc]
  constructor
  · rw [hend,hstart]
    exact hlower
  · calc
      schurBootstrapA1AtLevel lambda (m+N) -
          schurBootstrapA1AtLevel lambda m = f N-f 0 := by rw [hend,hstart]
      _ ≤ 4*u 0 := hupper
      _ ≤ (1/40000 : ℝ)*(1/2 : ℝ)^m := hsmall


/-- For every parameter in the bootstrap interval, the finite-level A1
characteristics form a Cauchy sequence.  The proof uses the already established
uniform tail estimate and the geometric decay of its bound.  This is convergence
of the characteristic values at fixed lambda; it does not yet assert convergence
or uniqueness of the finite-level roots. -/
theorem schurBootstrapA1AtLevel_cauchySeq
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper) :
    CauchySeq (fun n : ℕ => schurBootstrapA1AtLevel lambda n) := by
  let bound : ℕ → ℝ :=
    fun n => (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n
  have hdist :
      ∀ n m : ℕ, n ≤ m →
        dist
          (schurBootstrapA1AtLevel lambda n)
          (schurBootstrapA1AtLevel lambda m) ≤ bound n := by
    intro n m hnm
    have htail :=
      schurBootstrapA1AtLevel_tail_bound lambda hlambda n (m - n)
    have hindex : n + (m - n) = m := Nat.add_sub_of_le hnm
    rw [hindex] at htail
    calc
      dist
          (schurBootstrapA1AtLevel lambda n)
          (schurBootstrapA1AtLevel lambda m) =
        |schurBootstrapA1AtLevel lambda n -
          schurBootstrapA1AtLevel lambda m| := by
            rw [Real.dist_eq]
      _ = schurBootstrapA1AtLevel lambda m -
            schurBootstrapA1AtLevel lambda n := by
              have hle :
                  schurBootstrapA1AtLevel lambda n ≤
                    schurBootstrapA1AtLevel lambda m :=
                sub_nonneg.mp htail.1
              have hdiff :
                  schurBootstrapA1AtLevel lambda n -
                    schurBootstrapA1AtLevel lambda m ≤ 0 :=
                sub_nonpos.mpr hle
              rw [abs_of_nonpos hdiff]
              ring
      _ ≤ bound n := by
            simpa [bound] using htail.2
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbound : Tendsto bound atTop (𝓝 (0 : ℝ)) := by
    simpa [bound] using
      (tendsto_const_nhds.mul hpow)
  exact cauchySeq_of_le_tendsto_0' bound hdist hbound


/-- The finite-level A1 characteristics are uniformly Cauchy on the full
bootstrap parameter interval.  The tail estimate is uniform in the parameter;
the triangle inequality compares any two levels to the same base level N. -/
theorem schurBootstrapA1AtLevel_uniformCauchyOn :
    UniformCauchySeqOn
      (fun n lambda => schurBootstrapA1AtLevel lambda n)
      atTop
      (Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) := by
  let bound : ℕ → ℝ :=
    fun n => (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbound : Tendsto bound atTop (𝓝 (0 : ℝ)) := by
    simpa [bound] using
      (tendsto_const_nhds.mul hpow)
  have hdouble :
      Tendsto (fun n => bound n + bound n) atTop (𝓝 (0 : ℝ)) := by
    simpa using hbound.add hbound
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    (hdouble.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, ?_⟩
  intro m hm n hn lambda hlambda
  have hdistToBase (k : ℕ) (hk : N ≤ k) :
      dist
        (schurBootstrapA1AtLevel lambda k)
        (schurBootstrapA1AtLevel lambda N) ≤ bound N := by
    have htail :=
      schurBootstrapA1AtLevel_tail_bound lambda hlambda N (k - N)
    have hindex : N + (k - N) = k := Nat.add_sub_of_le hk
    rw [hindex] at htail
    calc
      dist
          (schurBootstrapA1AtLevel lambda k)
          (schurBootstrapA1AtLevel lambda N) =
        |schurBootstrapA1AtLevel lambda k -
          schurBootstrapA1AtLevel lambda N| := by
            rw [Real.dist_eq]
      _ = schurBootstrapA1AtLevel lambda k -
            schurBootstrapA1AtLevel lambda N :=
              abs_of_nonneg htail.1
      _ ≤ bound N := by
            simpa [bound] using htail.2
  have hmBound := hdistToBase m hm
  have hnBound := hdistToBase n hn
  have hnBound' :
      dist
        (schurBootstrapA1AtLevel lambda N)
        (schurBootstrapA1AtLevel lambda n) ≤ bound N := by
    simpa only [dist_comm] using hnBound
  calc
    dist
        (schurBootstrapA1AtLevel lambda m)
        (schurBootstrapA1AtLevel lambda n) ≤
      dist
          (schurBootstrapA1AtLevel lambda m)
          (schurBootstrapA1AtLevel lambda N) +
        dist
          (schurBootstrapA1AtLevel lambda N)
          (schurBootstrapA1AtLevel lambda n) :=
      dist_triangle _ _ _
    _ ≤ bound N + bound N := add_le_add hmBound hnBound'
    _ < ε := hN


/-- The pointwise limit of the finite-level A1 characteristics on the
bootstrap interval.  Outside the interval the function is set to zero, since
the convergence statement below is only asserted on that interval. -/
noncomputable def schurBootstrapA1AtLevel_limit (lambda : ℝ) : ℝ := by
  classical
  exact if hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper then
    Classical.choose
      (cauchySeq_tendsto_of_complete
        (schurBootstrapA1AtLevel_cauchySeq lambda hlambda))
  else 0

/-- At each parameter in the bootstrap interval, the finite-level
characteristics converge to the selected pointwise limit. -/
theorem schurBootstrapA1AtLevel_tendsto_limit
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper) :
    Tendsto
      (fun n : ℕ => schurBootstrapA1AtLevel lambda n)
      atTop
      (𝓝 (schurBootstrapA1AtLevel_limit lambda)) := by
  have hlim :=
    Classical.choose_spec
      (cauchySeq_tendsto_of_complete
        (schurBootstrapA1AtLevel_cauchySeq lambda hlambda))
  simpa [schurBootstrapA1AtLevel_limit, hlambda] using hlim

/-- The finite-level A1 characteristics converge uniformly on the full
bootstrap interval to their pointwise limit. -/
theorem schurBootstrapA1AtLevel_tendstoUniformlyOn_limit :
    TendstoUniformlyOn
      (fun n lambda => schurBootstrapA1AtLevel lambda n)
      (fun lambda => schurBootstrapA1AtLevel_limit lambda)
      atTop
      (Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) :=
  schurBootstrapA1AtLevel_uniformCauchyOn.tendstoUniformlyOn_of_tendsto
    (fun lambda hlambda =>
      schurBootstrapA1AtLevel_tendsto_limit lambda hlambda)


/-- Every finite-level A1 characteristic is continuous on the bootstrap
interval.  The existing finite-prefix continuity induction applies because
the full pivot nonvanishing theorem supplies both denominators at every step. -/
theorem schurBootstrapA1AtLevel_continuousOn (n : ℕ) :
    ContinuousOn
      (fun lambda => schurBootstrapA1AtLevel lambda n)
      (Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) := by
  apply schurBootstrapA1AtLevel_continuousOn_of_nonzero_pivots n
  intro lambda hlambda k hk
  exact schurBootstrap_all_pivots_nonzero lambda hlambda k

/-- The uniformly convergent limiting A1 characteristic is continuous on
the bootstrap interval. -/
theorem schurBootstrapA1AtLevel_limit_continuousOn :
    ContinuousOn
      schurBootstrapA1AtLevel_limit
      (Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) := by
  apply TendstoUniformlyOn.continuousOn
    schurBootstrapA1AtLevel_tendstoUniformlyOn_limit
  exact Filter.Frequently.of_forall
    schurBootstrapA1AtLevel_continuousOn


/-- The limiting A1 characteristic has at least one zero in the bootstrap
interval.  The finite-level endpoint signs pass to the pointwise limit, and
continuity of the uniform limit then gives a zero by the intermediate value
theorem.  This establishes existence, not uniqueness. -/
theorem schurBootstrapA1AtLevel_limit_exists_root :
    ∃ lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper,
      schurBootstrapA1AtLevel_limit lambda = 0 := by
  have hle :
      schurBootstrapLambdaLower ≤ schurBootstrapLambdaUpper := by
    norm_num [schurBootstrapLambdaLower, schurBootstrapLambdaUpper]
  have hleftMem :
      schurBootstrapLambdaLower ∈
        Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper :=
    ⟨le_rfl, hle⟩
  have hrightMem :
      schurBootstrapLambdaUpper ∈
        Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper :=
    ⟨hle, le_rfl⟩
  have hsigns := schurBootstrapEndpoints_A1_signs_all_finite_levels
  have hleft :
      0 ≤ schurBootstrapA1AtLevel_limit schurBootstrapLambdaLower := by
    apply ge_of_tendsto'
      (schurBootstrapA1AtLevel_tendsto_limit
        schurBootstrapLambdaLower hleftMem)
    intro n
    have hnonneg :
        0 ≤ schurBootstrapA1AtLevel schurBootstrapLambdaLower n := by
      simpa [schurBootstrapA1AtLevel, schurBoundaryTrajectory_add] using
        hsigns.1 n
    exact hnonneg
  have hright :
      schurBootstrapA1AtLevel_limit schurBootstrapLambdaUpper ≤ 0 := by
    apply le_of_tendsto'
      (schurBootstrapA1AtLevel_tendsto_limit
        schurBootstrapLambdaUpper hrightMem)
    intro n
    have hnegative :
        schurBootstrapA1AtLevel schurBootstrapLambdaUpper n < 0 := by
      simpa [schurBootstrapA1AtLevel, schurBoundaryTrajectory_add] using
        hsigns.2 n
    exact le_of_lt hnegative
  have hzero :
      (0 : ℝ) ∈ Set.Icc
        (schurBootstrapA1AtLevel_limit schurBootstrapLambdaUpper)
        (schurBootstrapA1AtLevel_limit schurBootstrapLambdaLower) :=
    ⟨hright, hleft⟩
  have himage :=
    intermediate_value_Icc' hle
      schurBootstrapA1AtLevel_limit_continuousOn
  obtain ⟨lambda, hlambda, hvalue⟩ := himage hzero
  exact ⟨lambda, hlambda, hvalue⟩


/-- The pointwise limit differs from a finite-level A1 characteristic by
at most the uniform geometric tail remaining after that level. -/
theorem schurBootstrapA1AtLevel_limit_tail_control
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper)
    (n : ℕ) :
    0 ≤ schurBootstrapA1AtLevel_limit lambda -
        schurBootstrapA1AtLevel lambda n ∧
      schurBootstrapA1AtLevel_limit lambda -
        schurBootstrapA1AtLevel lambda n ≤
          (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n := by
  have htail (m : ℕ) (hm : n ≤ m) :
      0 ≤ schurBootstrapA1AtLevel lambda m -
          schurBootstrapA1AtLevel lambda n ∧
        schurBootstrapA1AtLevel lambda m -
          schurBootstrapA1AtLevel lambda n ≤
            (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n := by
    have h :=
      schurBootstrapA1AtLevel_tail_bound lambda hlambda n (m - n)
    have hindex : n + (m - n) = m := Nat.add_sub_of_le hm
    rw [hindex] at h
    exact h
  have hlim :=
    Tendsto.sub_const
      (schurBootstrapA1AtLevel_tendsto_limit lambda hlambda)
      (schurBootstrapA1AtLevel lambda n)
  constructor
  · apply ge_of_tendsto hlim
    filter_upwards
      [eventually_atTop.2 ⟨n, fun m hm => (htail m hm).1⟩] with m hm
    exact hm
  · apply le_of_tendsto hlim
    filter_upwards
      [eventually_atTop.2 ⟨n, fun m hm => (htail m hm).2⟩] with m hm
    exact hm

/-- A canonical choice of one finite-level A1 root at every level. -/
noncomputable def schurBootstrapA1AtLevel_chosenRoot (n : ℕ) : ℝ :=
  Classical.choose (schurBootstrapA1AtLevel_exists_root n)

/-- The selected finite-level root lies in the bootstrap interval and
annihilates its own finite-level A1 characteristic. -/
theorem schurBootstrapA1AtLevel_chosenRoot_spec (n : ℕ) :
    schurBootstrapA1AtLevel_chosenRoot n ∈
        Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper ∧
      schurBootstrapA1AtLevel
        (schurBootstrapA1AtLevel_chosenRoot n) n = 0 :=
  Classical.choose_spec (schurBootstrapA1AtLevel_exists_root n)

/-- At a chosen finite-level root, the limiting characteristic is
nonnegative and its absolute value is bounded by the remaining geometric
tail. -/
theorem schurBootstrapA1AtLevel_chosenRoot_limit_bound (n : ℕ) :
    0 ≤ schurBootstrapA1AtLevel_limit
        (schurBootstrapA1AtLevel_chosenRoot n) ∧
      |schurBootstrapA1AtLevel_limit
          (schurBootstrapA1AtLevel_chosenRoot n)| ≤
        (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hroot := schurBootstrapA1AtLevel_chosenRoot_spec n
  have htail :=
    schurBootstrapA1AtLevel_limit_tail_control
      (schurBootstrapA1AtLevel_chosenRoot n) hroot.1 n
  rw [hroot.2] at htail
  have hnonneg :
      0 ≤ schurBootstrapA1AtLevel_limit
        (schurBootstrapA1AtLevel_chosenRoot n) := by
    simpa only [sub_zero] using htail.1
  have hupper :
      schurBootstrapA1AtLevel_limit
        (schurBootstrapA1AtLevel_chosenRoot n) ≤
          (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n := by
    simpa only [sub_zero] using htail.2
  constructor
  · exact hnonneg
  · calc
      |schurBootstrapA1AtLevel_limit
          (schurBootstrapA1AtLevel_chosenRoot n)| =
        schurBootstrapA1AtLevel_limit
          (schurBootstrapA1AtLevel_chosenRoot n) :=
            abs_of_nonneg hnonneg
      _ ≤ (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n := hupper

/-- Along any fixed choice of a finite-level root at every level, the value
of the limiting characteristic tends to zero.  Thus the finite roots are
uniformly controlled approximate roots of the limiting equation. -/
theorem schurBootstrapA1AtLevel_chosenRoots_limit_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        schurBootstrapA1AtLevel_limit
          (schurBootstrapA1AtLevel_chosenRoot n))
      atTop (𝓝 (0 : ℝ)) := by
  let bound : ℕ → ℝ :=
    fun n => (1 / 40000 : ℝ) * (1 / 2 : ℝ) ^ n
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbound : Tendsto bound atTop (𝓝 (0 : ℝ)) := by
    simpa [bound] using
      (tendsto_const_nhds.mul hpow)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards with n
    exact lt_of_lt_of_le ha
      (schurBootstrapA1AtLevel_chosenRoot_limit_bound n).1
  · intro a ha
    filter_upwards
      [hbound.eventually (gt_mem_nhds ha)] with n hn
    have hroot := schurBootstrapA1AtLevel_chosenRoot_limit_bound n
    exact lt_of_le_of_lt
      (le_trans (le_abs_self _) hroot.2) (by simpa [bound] using hn)

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Every sequence of selected finite-level A1 roots has a convergent
subsequence whose limit is a zero of the limiting characteristic.  Compactness
keeps the roots in the bootstrap interval; the uniform tail estimate makes
their limiting-characteristic values tend to zero; continuity identifies the
subsequence limit as an actual root. -/
theorem schurBootstrapA1AtLevel_chosenRoots_subseq_limit :
    ∃ lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Tendsto
          (fun n : ℕ =>
            schurBootstrapA1AtLevel_chosenRoot (φ n))
          atTop (𝓝 lambda) ∧
        schurBootstrapA1AtLevel_limit lambda = 0 := by
  have hcompact :
      IsCompact
        (Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) :=
    isCompact_Icc
  obtain ⟨lambda, hlambda, φ, hφ, hroots⟩ :=
    hcompact.tendsto_subseq
      (fun n =>
        (schurBootstrapA1AtLevel_chosenRoot_spec n).1)
  have hφtop : Tendsto φ atTop atTop :=
    StrictMono.tendsto_atTop hφ
  have hresidual :
      Tendsto
        (fun n : ℕ =>
          schurBootstrapA1AtLevel_limit
            (schurBootstrapA1AtLevel_chosenRoot (φ n)))
        atTop (𝓝 (0 : ℝ)) :=
    schurBootstrapA1AtLevel_chosenRoots_limit_tendsto_zero.comp hφtop
  have hrootsWithin :
      Tendsto
        (fun n : ℕ =>
          schurBootstrapA1AtLevel_chosenRoot (φ n))
        atTop
        (𝓝[Set.Icc schurBootstrapLambdaLower
          schurBootstrapLambdaUpper] lambda) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hroots, Filter.Eventually.of_forall
        (fun n =>
          (schurBootstrapA1AtLevel_chosenRoot_spec (φ n)).1)⟩
  have hlimit :
      Tendsto
        (fun n : ℕ =>
          schurBootstrapA1AtLevel_limit
            (schurBootstrapA1AtLevel_chosenRoot (φ n)))
        atTop
        (𝓝 (schurBootstrapA1AtLevel_limit lambda)) :=
    (schurBootstrapA1AtLevel_limit_continuousOn lambda hlambda).tendsto
      |>.comp hrootsWithin
  have hzero :
      schurBootstrapA1AtLevel_limit lambda = 0 :=
    tendsto_nhds_unique hlimit hresidual
  exact ⟨lambda, hlambda, φ, hφ, hroots, hzero⟩


/-- If the level-n A1 characteristic vanishes at a parameter in the
bootstrap interval, then the next-level characteristic has a zero between
that parameter and the upper endpoint.  The tail increment is nonnegative
at the old root, while the right endpoint remains strictly negative. -/
theorem schurBootstrapA1AtLevel_next_root_exists
    (n : ℕ)
    (lambda : ℝ)
    (hlambda :
      lambda ∈ Set.Icc schurBootstrapLambdaLower
        schurBootstrapLambdaUpper)
    (hroot : schurBootstrapA1AtLevel lambda n = 0) :
    ∃ mu ∈ Set.Icc lambda schurBootstrapLambdaUpper,
      schurBootstrapA1AtLevel mu (n + 1) = 0 := by
  have htail :=
    schurBootstrapA1AtLevel_tail_bound lambda hlambda n 1
  have hleft :
      0 ≤ schurBootstrapA1AtLevel lambda (n + 1) := by
    simpa [hroot] using htail.1
  have hsigns := schurBootstrapEndpoints_A1_signs_all_finite_levels
  have hright :
      schurBootstrapA1AtLevel schurBootstrapLambdaUpper (n + 1) < 0 := by
    simpa [schurBootstrapA1AtLevel, schurBoundaryTrajectory_add] using
      hsigns.2 (n + 1)
  have hle : lambda ≤ schurBootstrapLambdaUpper := hlambda.2
  have hcontinuousAll :=
    schurBootstrapA1AtLevel_continuousOn (n + 1)
  have hsubset :
      Set.Icc lambda schurBootstrapLambdaUpper ⊆
        Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper := by
    intro x hx
    exact ⟨le_trans hlambda.1 hx.1, hx.2⟩
  have hcontinuous :=
    hcontinuousAll.mono hsubset
  have hzero :
      (0 : ℝ) ∈ Set.Icc
        (schurBootstrapA1AtLevel schurBootstrapLambdaUpper (n + 1))
        (schurBootstrapA1AtLevel lambda (n + 1)) :=
    ⟨le_of_lt hright, hleft⟩
  have himage :=
    intermediate_value_Icc' hle hcontinuous
  rcases himage hzero with ⟨mu, hmu, hvalue⟩
  exact ⟨mu, hmu, hvalue⟩


/-- The subtype of parameters that are roots of the level-n A1
characteristic inside the bootstrap interval. -/
abbrev schurBootstrapA1RootAtLevel (n : ℕ) :=
  {lambda : ℝ //
    lambda ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper ∧
      schurBootstrapA1AtLevel lambda n = 0}

/-- Choose a root of the next level no smaller than a given root of the
current level. -/
noncomputable def schurBootstrapA1AtLevel_rootStep
    (n : ℕ)
    (root : schurBootstrapA1RootAtLevel n) :
    schurBootstrapA1RootAtLevel (n + 1) := by
  let hnext :=
    schurBootstrapA1AtLevel_next_root_exists
      n root.1 root.property.1 root.property.2
  let mu := Classical.choose hnext
  have hmu := Classical.choose_spec hnext
  refine ⟨mu, ?_⟩
  exact ⟨⟨le_trans root.property.1.1 hmu.1.1, hmu.1.2⟩, hmu.2⟩

/-- Every root step moves weakly to the right. -/
theorem schurBootstrapA1AtLevel_rootStep_ge
    (n : ℕ)
    (root : schurBootstrapA1RootAtLevel n) :
    root.1 ≤ (schurBootstrapA1AtLevel_rootStep n root).1 := by
  change root.1 ≤ Classical.choose
    (schurBootstrapA1AtLevel_next_root_exists
      n root.1 root.property.1 root.property.2)
  exact
    (Classical.choose_spec
      (schurBootstrapA1AtLevel_next_root_exists
        n root.1 root.property.1 root.property.2)).1.1

/-- A coherently selected root at each level, with each new root chosen
to the right of the preceding one. -/
noncomputable def schurBootstrapA1AtLevel_rootSequence :
    (n : ℕ) → schurBootstrapA1RootAtLevel n
  | 0 =>
      ⟨schurBootstrapA1AtLevel_chosenRoot 0,
        schurBootstrapA1AtLevel_chosenRoot_spec 0⟩
  | n + 1 =>
      schurBootstrapA1AtLevel_rootStep n
        (schurBootstrapA1AtLevel_rootSequence n)

/-- The selected root parameters form a nondecreasing sequence. -/
theorem schurBootstrapA1AtLevel_rootSequence_monotone :
    Monotone
      (fun n : ℕ =>
        (schurBootstrapA1AtLevel_rootSequence n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  change
    (schurBootstrapA1AtLevel_rootSequence n).1 ≤
      (schurBootstrapA1AtLevel_rootStep n
        (schurBootstrapA1AtLevel_rootSequence n)).1
  exact schurBootstrapA1AtLevel_rootStep_ge n
    (schurBootstrapA1AtLevel_rootSequence n)

/-- The monotone root sequence is bounded above by the bootstrap
interval's right endpoint. -/
theorem schurBootstrapA1AtLevel_rootSequence_bddAbove :
    BddAbove
      (Set.range fun n : ℕ =>
        (schurBootstrapA1AtLevel_rootSequence n).1) := by
  refine ⟨schurBootstrapLambdaUpper, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (schurBootstrapA1AtLevel_rootSequence n).property.1.2

/-- The coherently selected finite-level roots converge to their
supremum. -/
theorem schurBootstrapA1AtLevel_rootSequence_tendsto :
    Tendsto
      (fun n : ℕ =>
        (schurBootstrapA1AtLevel_rootSequence n).1)
      atTop
      (𝓝 (⨆ n : ℕ,
        (schurBootstrapA1AtLevel_rootSequence n).1)) :=
  tendsto_atTop_ciSup
    schurBootstrapA1AtLevel_rootSequence_monotone
    schurBootstrapA1AtLevel_rootSequence_bddAbove

end PhiGenesis.SpectralGap
