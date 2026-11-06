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
def schurNextDiagonal (a b c : ℝ) : ℝ :=
  a - 2 * b ^ 2 * (c + b) / (c * (c + 3 * b))

/-- Off-diagonal entry of the next three-corner Schur matrix. -/
def schurNextOffDiagonal (b c : ℝ) : ℝ :=
  -b ^ 2 * (c - b) / (c * (c + 3 * b))

/-- At an A1 root, the next-level A1 characteristic evaluated at the
old root is exactly the displayed rational expression. -/
theorem schurNextA1_at_old_root (a b c : ℝ)
    (hA1 : a + 2 * b = 0) (hc : c ≠ 0) (hc3 : c + 3 * b ≠ 0) :
    schurNextDiagonal a b c + 2 * schurNextOffDiagonal b c =
      -2 * b * (c + 5 * b) / (c + 3 * b) := by
  unfold schurNextDiagonal schurNextOffDiagonal
  have ha : a = -2 * b := by linarith
  rw [ha]
  field_simp [hc, hc3]
  ring

/-- The off-diagonal Schur coefficient changes quadratically in b,
with an exact finite-level prefactor. -/
theorem schurNextOffDiagonal_div_sq (b c : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hc3 : c + 3 * b ≠ 0) :
    schurNextOffDiagonal b c / b ^ 2 =
      -(c - b) / (c * (c + 3 * b)) := by
  unfold schurNextOffDiagonal
  field_simp [hb, hc, hc3]
  ring

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
  · change 0 ≤ (c + b) + 2 * b
    exact hc3
  · change 0 ≤ (c + b) - b
    exact hc

end PhiGenesis.SpectralGap
