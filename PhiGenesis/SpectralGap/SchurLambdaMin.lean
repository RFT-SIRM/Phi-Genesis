import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurSpectralBounds

namespace PhiGenesis.SpectralGap

/-- The shifted form is the unshifted form minus `lam` times the squared norm. -/
theorem sgForm_shift (m : Nat) (lam : ℝ) (x : SGVertex m → ℝ) :
    sgSignlessShiftedBilinearForm m lam x x =
      sgSignlessShiftedBilinearForm m 0 x x - lam * ∑ v, (x v) ^ 2 := by
  classical
  unfold sgSignlessShiftedBilinearForm
  have hinner : ∀ u : SGVertex m,
      (∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * x v) =
      (∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          (0 : ℝ) • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * x v) -
        lam * x u := by
    intro u
    have h : ∀ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * x v =
        (sgSignlessLaplacianMatrix m -
          (0 : ℝ) • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * x v -
          (if u = v then lam * x v else 0) := by
      intro v
      by_cases hv : u = v
      · subst hv
        simp [Matrix.sub_apply, Matrix.one_apply]
        ring
      · simp [Matrix.sub_apply, Matrix.one_apply, hv]
    rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_sub_distrib,
      Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun u _ => by rw [hinner u])]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Uniqueness of a "Rayleigh minimum": two values that both bound the form from below
and are both attained on nonzero vectors coincide. -/
theorem sgRayleighMin_unique (m : Nat) (mu nu : ℝ)
    (hmu : ∀ y : SGVertex m → ℝ, 0 ≤ sgSignlessShiftedBilinearForm m mu y y)
    (hnu : ∀ y : SGVertex m → ℝ, 0 ≤ sgSignlessShiftedBilinearForm m nu y y)
    (hmu0 : ∃ x : SGVertex m → ℝ, 0 < ∑ v, (x v) ^ 2 ∧
      sgSignlessShiftedBilinearForm m mu x x = 0)
    (hnu0 : ∃ x : SGVertex m → ℝ, 0 < ∑ v, (x v) ^ 2 ∧
      sgSignlessShiftedBilinearForm m nu x x = 0) :
    mu = nu := by
  obtain ⟨x, hxpos, hx0⟩ := hmu0
  obtain ⟨x', hxpos', hx0'⟩ := hnu0
  have h1 := hnu x
  have h2 := hmu x'
  rw [sgForm_shift] at h1 h2 hx0 hx0'
  have hlt1 : nu * ∑ v, (x v) ^ 2 ≤ mu * ∑ v, (x v) ^ 2 := by linarith
  have hlt2 : mu * ∑ v, (x' v) ^ 2 ≤ nu * ∑ v, (x' v) ^ 2 := by linarith
  have a1 : nu ≤ mu := le_of_mul_le_mul_right hlt1 hxpos
  have a2 : mu ≤ nu := le_of_mul_le_mul_right hlt2 hxpos'
  exact le_antisymm a2 a1

/-- At an A1 root in the window the form is nonnegative on all vectors and vanishes on a
nonzero vector. -/
theorem sgRayleighAtRoot (n : ℕ) (r : ℝ)
    (hr : r ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hroot : schurBootstrapA1AtLevel r n = 0) :
    (∀ y : SGVertex (6 + n) → ℝ, 0 ≤ sgSignlessShiftedBilinearForm (6 + n) r y y) ∧
    (∃ x : SGVertex (6 + n) → ℝ, 0 < ∑ v, (x v) ^ 2 ∧
      sgSignlessShiftedBilinearForm (6 + n) r x x = 0) := by
  classical
  have hwin := schurBootstrapEndpoints_in_parameter_window
  have hlam_lower : (1309 / 1000 : ℝ) ≤ r := le_trans hwin.1 hr.1
  have hlam_upper : r ≤ (131 / 100 : ℝ) := le_trans hr.2 hwin.2.2.2
  have hresp := sgCornerResponse_trajectory_bootstrap r hr (6 + n)
  have hD := sgDirichletNonneg_bootstrap r hr (6 + n)
  have hstart := schurBootstrap_levelThree_state_box r hr
  have hstate := schurBoundaryTrajectory_coarse_state_box r
    (schurBoundaryTrajectory r (2 - r, 1) 3).1
    (schurBoundaryTrajectory r (2 - r, 1) 3).2
    hstart.1 hstart.2.1 hstart.2.2 hlam_lower hlam_upper (3 + n)
  have e : 6 + n = 3 + (3 + n) := by omega
  have htraj : schurBoundaryTrajectory r (2 - r, 1) (6 + n) =
      schurBoundaryTrajectory r (schurBoundaryTrajectory r (2 - r, 1) 3) (3 + n) := by
    rw [e, schurBoundaryTrajectory_add]
  have hb : (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2 ≤ 0 := by
    rw [htraj]; exact hstate.2.2
  have hA : (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).1 +
      2 * (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2 = 0 := hroot
  have hE : 0 ≤ (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).1 -
      (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2 := by linarith
  constructor
  · intro y
    exact sgForm_nonneg_of_response (6 + n) r _ _ hD hresp (le_of_eq hA.symm) hE y
  · obtain ⟨x, hx1, hx2, hx3⟩ := hresp (fun _ => (1 : ℝ))
    refine ⟨x, ?_, ?_⟩
    · have h1 : x (sgLevelOuterCorner (6 + n) TriangleCorner.leftBase) = 1 :=
        hx1 TriangleCorner.leftBase
      have hle : (x (sgLevelOuterCorner (6 + n) TriangleCorner.leftBase)) ^ 2 ≤
          ∑ v, (x v) ^ 2 :=
        Finset.single_le_sum (f := fun v => (x v) ^ 2)
          (fun v _ => sq_nonneg (x v)) (Finset.mem_univ _)
      rw [h1] at hle
      linarith
    · have hself := sgForm_harmonic_self (6 + n) r _ _ x (fun _ => (1 : ℝ))
        hx1 hx2 hx3
      rw [hself]
      simp only [sum_triangleCorner]
      nlinarith [hA]

/-- Uniqueness of the A1 root of level `6 + n` in the bootstrap window. -/
theorem schurBootstrapA1Root_unique (n : ℕ) (r r' : ℝ)
    (hr : r ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hr' : r' ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hroot : schurBootstrapA1AtLevel r n = 0)
    (hroot' : schurBootstrapA1AtLevel r' n = 0) : r = r' := by
  obtain ⟨h1, h2⟩ := sgRayleighAtRoot n r hr hroot
  obtain ⟨h1', h2'⟩ := sgRayleighAtRoot n r' hr' hroot'
  exact sgRayleighMin_unique (6 + n) r r' h1 h1' h2 h2'

/-- The coherently selected root sequence coincides with the canonical choice. -/
theorem schurBootstrapA1AtLevel_rootSequence_eq_chosenRoot (n : ℕ) :
    (schurBootstrapA1AtLevel_rootSequence n).1 = schurBootstrapA1AtLevel_chosenRoot n := by
  obtain ⟨hmem, hz⟩ := (schurBootstrapA1AtLevel_rootSequence n).property
  obtain ⟨hmem', hz'⟩ := schurBootstrapA1AtLevel_chosenRoot_spec n
  exact schurBootstrapA1Root_unique n _ _ hmem hmem' hz hz'

/-- The canonical A1 roots, i.e. the Rayleigh minima of level `6 + n`, converge. -/
theorem schurBootstrapA1AtLevel_chosenRoot_tendsto :
    Filter.Tendsto schurBootstrapA1AtLevel_chosenRoot Filter.atTop
      (nhds schurBootstrapA1AtLevel_rootLimit) := by
  have h := schurBootstrapA1AtLevel_rootSequence_tendsto_rootLimit
  have e : (fun n : ℕ => (schurBootstrapA1AtLevel_rootSequence n).1) =
      schurBootstrapA1AtLevel_chosenRoot :=
    funext schurBootstrapA1AtLevel_rootSequence_eq_chosenRoot
  rw [e] at h
  exact h

end PhiGenesis.SpectralGap
