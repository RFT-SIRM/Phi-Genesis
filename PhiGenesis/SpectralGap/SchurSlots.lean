import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurBridge

/-!
# Bridge, step B2b (combinatorial half): edge sums over face-edge slots

`faceGraphEdges` is the image of the injective endpoint map on face-edge slots, so sums over
graph edges are sums over slots.
-/

namespace PhiGenesis.SpectralGap

/-- The signless matrix entry is a sum over face-edge slots. -/
theorem sgSignlessLaplacianMatrix_eq_slotSum (m : Nat) (u v : SGVertex m) :
    sgSignlessLaplacianMatrix m u v =
      ∑ p : (Fin m → Fin 3) × TriangleEdge,
        sgEdgeIndicator m (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p) u *
          sgEdgeIndicator m (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p) v := by
  unfold sgSignlessLaplacianMatrix faceGraphEdges
  exact Finset.sum_image (fun p _ q _ h => sgFaceEdgeEndpoints_injective m h)

end PhiGenesis.SpectralGap

namespace PhiGenesis.SpectralGap

/-- Every edge slot in a level-(m+1) face is the translate of
the corresponding edge slot in its level-m tail face. -/
theorem sgFaceEdgeCoords_succ (m : Nat)
    (w : Fin (m + 1) → Fin 3) (e : TriangleEdge) :
    sgFaceEdgeCoords (m + 1) (w, e) =
      (sgAddOffset m (w 0)
          (sgFaceEdgeCoords m (sgFaceTail w, e)).1,
       sgAddOffset m (w 0)
          (sgFaceEdgeCoords m (sgFaceTail w, e)).2) := by
  cases e <;>
    simp [sgFaceEdgeCoords, sgFaceCornerCoords_succ, sgAddOffset]

end PhiGenesis.SpectralGap

namespace PhiGenesis.SpectralGap

/-- The vertex embedding of one level-m child copy into level m+1. -/
def sgChildVertex (m : Nat) (child : Fin 3) (v : SGVertex m) :
    SGVertex (m + 1) :=
  ⟨sgAddOffset m child v.1, by
    classical
    obtain ⟨p, hp⟩ := sgCornerVertex_surjective m v
    rcases p with ⟨f, c⟩
    have hv : sgFaceCornerCoords m (f, c) = v.1 :=
      congrArg Subtype.val hp
    change sgAddOffset m child v.1 ∈
      Finset.univ.image (sgFaceCornerCoords (m + 1))
    rw [← hv]
    exact Finset.mem_image.mpr
      ⟨(Fin.cons child f, c), Finset.mem_univ _,
        sgFaceCornerCoords_succ m (Fin.cons child f) c⟩
  ⟩

/-- Each translated child-copy vertex map is injective. -/
theorem sgChildVertex_injective (m : Nat) (child : Fin 3) :
    Function.Injective (sgChildVertex m child) := by
  intro u v huv
  have hcoord :
      sgAddOffset m child u.1 = sgAddOffset m child v.1 :=
    congrArg Subtype.val huv
  have hx := congrArg Prod.fst hcoord
  have hy := congrArg Prod.snd hcoord
  apply Subtype.ext
  apply Prod.ext
  · change (u.1).1 + (sgChildOffset m child).1 =
      (v.1).1 + (sgChildOffset m child).1 at hx
    omega
  · change (u.1).2 + (sgChildOffset m child).2 =
      (v.1).2 + (sgChildOffset m child).2 at hy
    omega

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child vertex embedding preserves every face-corner slot. -/
theorem sgChildVertex_corner (m : Nat) (child : Fin 3)
    (f : Fin m → Fin 3) (c : TriangleCorner) :
    sgChildVertex m child (sgCornerVertex m (f, c)) =
      sgCornerVertex (m + 1) (Fin.cons child f, c) := by
  apply Subtype.ext
  change sgAddOffset m child (sgFaceCornerCoords m (f, c)) =
    sgFaceCornerCoords (m + 1) (Fin.cons child f, c)
  have htail : sgFaceTail (Fin.cons child f) = f := by
    funext i
    rfl
  have h := (sgFaceCornerCoords_succ m (Fin.cons child f) c).symm
  rw [htail] at h
  exact h

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child vertex embedding preserves the ordered endpoints
of every face-edge slot. -/
theorem sgChildVertex_edgeEndpoints (m : Nat) (child : Fin 3)
    (f : Fin m → Fin 3) (e : TriangleEdge) :
    (sgChildVertex m child
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
          (f, e)).1,
      sgChildVertex m child
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
          (f, e)).2) =
      faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
        (sgFaceC (m + 1)) (Fin.cons child f, e) := by
  cases e <;>
    simp [faceEdgeEndpoints, sgFaceA, sgFaceB, sgFaceC,
      sgChildVertex_corner]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Splits a level-(m+1) face address into its leading child
and its level-m tail address. -/
def sgFaceAddressEquiv (m : Nat) :
    (Fin (m + 1) → Fin 3) ≃ (Fin 3 × (Fin m → Fin 3)) where
  toFun w := (w 0, sgFaceTail w)
  invFun p := Fin.cons p.1 p.2
  left_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨child, f⟩
    apply Prod.ext
    · rfl
    · funext i
      rfl

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Reindexes level-(m+1) face-edge slots by a child
and a level-m face-edge slot. -/
def sgFaceEdgeSlotEquiv (m : Nat) :
    ((Fin (m + 1) → Fin 3) × TriangleEdge) ≃
      (Fin 3 × ((Fin m → Fin 3) × TriangleEdge)) where
  toFun p := (p.1 0, (sgFaceTail p.1, p.2))
  invFun q := (Fin.cons q.1 q.2.1, q.2.2)
  left_inv p := by
    rcases p with ⟨w, e⟩
    apply Prod.ext
    · exact (sgFaceAddressEquiv m).left_inv w
    · rfl
  right_inv q := by
    rcases q with ⟨child, f, e⟩
    rfl

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Every level-(m+1) edge is the image of the corresponding
level-m edge in the child specified by its leading address digit. -/
theorem sgFaceEdgeEndpoints_eq_child (m : Nat)
    (w : Fin (m + 1) → Fin 3) (e : TriangleEdge) :
    faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
        (sgFaceC (m + 1)) (w, e) =
      (sgChildVertex m (w 0)
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            (sgFaceTail w, e)).1,
       sgChildVertex m (w 0)
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            (sgFaceTail w, e)).2) := by
  have haddr : w = Fin.cons (w 0) (sgFaceTail w) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  have hface :
      faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
          (sgFaceC (m + 1)) (w, e) =
        faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
          (sgFaceC (m + 1))
          (Fin.cons (w 0) (sgFaceTail w), e) :=
    congrArg
      (fun a : Fin (m + 1) → Fin 3 =>
        faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
          (sgFaceC (m + 1)) (a, e))
      haddr
  calc
    faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
        (sgFaceC (m + 1)) (w, e) =
      faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
        (sgFaceC (m + 1))
        (Fin.cons (w 0) (sgFaceTail w), e) := hface
    _ = _ :=
      (sgChildVertex_edgeEndpoints m (w 0) (sgFaceTail w) e).symm

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The level-(m+1) signless matrix is the sum of the
three child-copy edge contributions, reindexed by child and old slot. -/
theorem sgSignlessLaplacianMatrix_eq_childSlotSum (m : Nat)
    (u v : SGVertex (m + 1)) :
    sgSignlessLaplacianMatrix (m + 1) u v =
      ∑ q : Fin 3 × ((Fin m → Fin 3) × TriangleEdge),
        sgEdgeIndicator (m + 1)
          (sgChildVertex m q.1
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              q.2).1,
           sgChildVertex m q.1
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              q.2).2) u *
        sgEdgeIndicator (m + 1)
          (sgChildVertex m q.1
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              q.2).1,
           sgChildVertex m q.1
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              q.2).2) v := by
  rw [sgSignlessLaplacianMatrix_eq_slotSum]
  exact Fintype.sum_equiv
    (sgFaceEdgeSlotEquiv m)
    (fun s =>
      sgEdgeIndicator (m + 1)
        (faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
          (sgFaceC (m + 1)) s) u *
      sgEdgeIndicator (m + 1)
        (faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
          (sgFaceC (m + 1)) s) v)
    (fun q =>
      sgEdgeIndicator (m + 1)
        (sgChildVertex m q.1
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            q.2).1,
         sgChildVertex m q.1
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            q.2).2) u *
      sgEdgeIndicator (m + 1)
        (sgChildVertex m q.1
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            q.2).1,
         sgChildVertex m q.1
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            q.2).2) v)
    (by
      rintro ⟨w, e⟩
      change
        sgEdgeIndicator (m + 1)
          (faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
            (sgFaceC (m + 1)) (w, e)) u *
        sgEdgeIndicator (m + 1)
          (faceEdgeEndpoints (sgFaceA (m + 1)) (sgFaceB (m + 1))
            (sgFaceC (m + 1)) (w, e)) v =
        sgEdgeIndicator (m + 1)
          (sgChildVertex m (w 0)
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              (sgFaceTail w, e)).1,
           sgChildVertex m (w 0)
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              (sgFaceTail w, e)).2) u *
        sgEdgeIndicator (m + 1)
          (sgChildVertex m (w 0)
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              (sgFaceTail w, e)).1,
           sgChildVertex m (w 0)
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              (sgFaceTail w, e)).2) v
      rw [sgFaceEdgeEndpoints_eq_child m w e])

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The coordinate sum of every level-m face origin
is strictly smaller than the side length 2^m. -/
theorem sgFaceOrigin_sum_lt :
    ∀ m (w : Fin m → Fin 3),
      (sgFaceOrigin m w).1 + (sgFaceOrigin m w).2 < 2 ^ m
  | 0, _ => by
      simp [sgFaceOrigin]
  | m + 1, w => by
      have htail := sgFaceOrigin_sum_lt m (sgFaceTail w)
      have hoff :
          (sgChildOffset m (w 0)).1 +
            (sgChildOffset m (w 0)).2 ≤ 2 ^ m := by
        simp [sgChildOffset]
        split_ifs <;> omega
      simp only [sgFaceOrigin, sgAddOffset]
      rw [pow_succ]
      omega

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The coordinate sum of every level-m gasket vertex
is at most the side length 2^m. -/
theorem sgVertex_coord_sum_le (m : Nat) (v : SGVertex m) :
    v.1.1 + v.1.2 ≤ 2 ^ m := by
  obtain ⟨p, hp⟩ := sgCornerVertex_surjective m v
  rcases p with ⟨f, c⟩
  have hcoord : sgFaceCornerCoords m (f, c) = v.1 :=
    congrArg Subtype.val hp
  rw [← hcoord]
  cases c <;> simp [sgFaceCornerCoords] <;>
    (have h := sgFaceOrigin_sum_lt m f; omega)

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child copies 0 and 1 can intersect only at
the common vertex (2^m, 0). -/
theorem sgChildVertex_intersection_zero_one (m : Nat)
    (u v : SGVertex m)
    (h : sgChildVertex m 0 u = sgChildVertex m 1 v) :
    u.1 = (2 ^ m, 0) ∧ v.1 = (0, 0) := by
  have hcoord :
      sgAddOffset m 0 u.1 = sgAddOffset m 1 v.1 :=
    congrArg Subtype.val h
  have hx := congrArg Prod.fst hcoord
  have hy := congrArg Prod.snd hcoord
  have hu := sgVertex_coord_sum_le m u
  change sgAddOffset m 0 u.1 = sgAddOffset m 1 v.1 at hcoord
  simp [sgAddOffset, sgChildOffset] at hx hy
  constructor
  · apply Prod.ext <;> omega
  · apply Prod.ext <;> omega

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child copies 0 and 2 can intersect only at
the common vertex (0, 2^m). -/
theorem sgChildVertex_intersection_zero_two (m : Nat)
    (u v : SGVertex m)
    (h : sgChildVertex m 0 u = sgChildVertex m 2 v) :
    u.1 = (0, 2 ^ m) ∧ v.1 = (0, 0) := by
  have hcoord :
      sgAddOffset m 0 u.1 = sgAddOffset m 2 v.1 :=
    congrArg Subtype.val h
  have hx := congrArg Prod.fst hcoord
  have hy := congrArg Prod.snd hcoord
  have hu := sgVertex_coord_sum_le m u
  have hv := sgVertex_coord_sum_le m v
  simp [sgAddOffset, sgChildOffset] at hx hy
  constructor
  · apply Prod.ext <;> omega
  · apply Prod.ext <;> omega

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child copies 1 and 2 can intersect only at
the common vertex (2^m, 2^m). -/
theorem sgChildVertex_intersection_one_two (m : Nat)
    (u v : SGVertex m)
    (h : sgChildVertex m 1 u = sgChildVertex m 2 v) :
    u.1 = (0, 2 ^ m) ∧ v.1 = (2 ^ m, 0) := by
  have hcoord :
      sgAddOffset m 1 u.1 = sgAddOffset m 2 v.1 :=
    congrArg Subtype.val h
  have hx := congrArg Prod.fst hcoord
  have hy := congrArg Prod.snd hcoord
  have hu := sgVertex_coord_sum_le m u
  have hv := sgVertex_coord_sum_le m v
  simp [sgAddOffset, sgChildOffset] at hx hy
  constructor
  · apply Prod.ext <;> omega
  · apply Prod.ext <;> omega

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The all-zero address has the origin as its left-base corner. -/
theorem sgFaceCornerCoords_all_zero_left (m : Nat) :
    sgFaceCornerCoords m
      ((fun _ : Fin m => (0 : Fin 3)), .leftBase) = (0, 0) := by
  induction m with
  | zero =>
      simp [sgFaceCornerCoords, sgFaceOrigin]
  | succ m ih =>
      rw [sgFaceCornerCoords_succ m
        (fun _ : Fin (m + 1) => (0 : Fin 3)) .leftBase]
      simpa [sgFaceTail, sgAddOffset, sgChildOffset, ih]

/-- The all-one address has the rightmost point as its right-base corner. -/
theorem sgFaceCornerCoords_all_one_right (m : Nat) :
    sgFaceCornerCoords m
      ((fun _ : Fin m => (1 : Fin 3)), .rightBase) = (2 ^ m, 0) := by
  induction m with
  | zero =>
      simp [sgFaceCornerCoords, sgFaceOrigin]
  | succ m ih =>
      rw [sgFaceCornerCoords_succ m
        (fun _ : Fin (m + 1) => (1 : Fin 3)) .rightBase]
      have htail :
          sgFaceTail (fun _ : Fin (m + 1) => (1 : Fin 3)) =
            (fun _ : Fin m => (1 : Fin 3)) := by
        funext i
        rfl
      rw [htail, ih]
      simp [sgAddOffset, sgChildOffset, pow_succ, Nat.mul_two]

/-- The all-two address has the topmost point as its apex corner. -/
theorem sgFaceCornerCoords_all_two_apex (m : Nat) :
    sgFaceCornerCoords m
      ((fun _ : Fin m => (2 : Fin 3)), .apex) = (0, 2 ^ m) := by
  induction m with
  | zero =>
      simp [sgFaceCornerCoords, sgFaceOrigin]
  | succ m ih =>
      rw [sgFaceCornerCoords_succ m
        (fun _ : Fin (m + 1) => (2 : Fin 3)) .apex]
      have htail :
          sgFaceTail (fun _ : Fin (m + 1) => (2 : Fin 3)) =
            (fun _ : Fin m => (2 : Fin 3)) := by
        funext i
        rfl
      rw [htail, ih]
      simp [sgAddOffset, sgChildOffset, pow_succ, Nat.mul_two]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child copies 0 and 1 do share their common boundary vertex. -/
theorem sgChildVertex_intersection_zero_one_exists (m : Nat) :
    ∃ u v : SGVertex m,
      sgChildVertex m 0 u = sgChildVertex m 1 v := by
  refine ⟨
    sgCornerVertex m ((fun _ : Fin m => (1 : Fin 3)), .rightBase),
    sgCornerVertex m ((fun _ : Fin m => (0 : Fin 3)), .leftBase),
    ?_⟩
  apply Subtype.ext
  change sgAddOffset m 0
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (1 : Fin 3)), .rightBase)) =
    sgAddOffset m 1
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (0 : Fin 3)), .leftBase))
  rw [sgFaceCornerCoords_all_one_right,
      sgFaceCornerCoords_all_zero_left]
  simp [sgAddOffset, sgChildOffset]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child copies 0 and 2 do share their common boundary vertex. -/
theorem sgChildVertex_intersection_zero_two_exists (m : Nat) :
    ∃ u v : SGVertex m,
      sgChildVertex m 0 u = sgChildVertex m 2 v := by
  refine ⟨
    sgCornerVertex m ((fun _ : Fin m => (2 : Fin 3)), .apex),
    sgCornerVertex m ((fun _ : Fin m => (0 : Fin 3)), .leftBase),
    ?_⟩
  apply Subtype.ext
  change sgAddOffset m 0
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (2 : Fin 3)), .apex)) =
    sgAddOffset m 2
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (0 : Fin 3)), .leftBase))
  rw [sgFaceCornerCoords_all_two_apex,
      sgFaceCornerCoords_all_zero_left]
  simp [sgAddOffset, sgChildOffset]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The child copies 1 and 2 do share their common boundary vertex. -/
theorem sgChildVertex_intersection_one_two_exists (m : Nat) :
    ∃ u v : SGVertex m,
      sgChildVertex m 1 u = sgChildVertex m 2 v := by
  refine ⟨
    sgCornerVertex m ((fun _ : Fin m => (2 : Fin 3)), .apex),
    sgCornerVertex m ((fun _ : Fin m => (1 : Fin 3)), .rightBase),
    ?_⟩
  apply Subtype.ext
  change sgAddOffset m 1
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (2 : Fin 3)), .apex)) =
    sgAddOffset m 2
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (1 : Fin 3)), .rightBase))
  rw [sgFaceCornerCoords_all_two_apex,
      sgFaceCornerCoords_all_one_right]
  simp [sgAddOffset, sgChildOffset]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Exact characterization of the intersection of child copies 0 and 1. -/
theorem sgChildVertex_intersection_zero_one_iff (m : Nat)
    (u v : SGVertex m) :
    sgChildVertex m 0 u = sgChildVertex m 1 v ↔
      u.1 = (2 ^ m, 0) ∧ v.1 = (0, 0) := by
  constructor
  · exact sgChildVertex_intersection_zero_one m u v
  · rintro ⟨hu, hv⟩
    apply Subtype.ext
    change sgAddOffset m 0 u.1 = sgAddOffset m 1 v.1
    rw [hu, hv]
    simp [sgAddOffset, sgChildOffset]

/-- Exact characterization of the intersection of child copies 0 and 2. -/
theorem sgChildVertex_intersection_zero_two_iff (m : Nat)
    (u v : SGVertex m) :
    sgChildVertex m 0 u = sgChildVertex m 2 v ↔
      u.1 = (0, 2 ^ m) ∧ v.1 = (0, 0) := by
  constructor
  · exact sgChildVertex_intersection_zero_two m u v
  · rintro ⟨hu, hv⟩
    apply Subtype.ext
    change sgAddOffset m 0 u.1 = sgAddOffset m 2 v.1
    rw [hu, hv]
    simp [sgAddOffset, sgChildOffset]

/-- Exact characterization of the intersection of child copies 1 and 2. -/
theorem sgChildVertex_intersection_one_two_iff (m : Nat)
    (u v : SGVertex m) :
    sgChildVertex m 1 u = sgChildVertex m 2 v ↔
      u.1 = (0, 2 ^ m) ∧ v.1 = (2 ^ m, 0) := by
  constructor
  · exact sgChildVertex_intersection_one_two m u v
  · rintro ⟨hu, hv⟩
    apply Subtype.ext
    change sgAddOffset m 1 u.1 = sgAddOffset m 2 v.1
    rw [hu, hv]
    simp [sgAddOffset, sgChildOffset]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Every level-(m+1) vertex belongs to at least one
of the three translated level-m child copies. -/
theorem sgChildVertex_surjective_union (m : Nat) :
    Function.Surjective
      (fun p : Fin 3 × SGVertex m =>
        sgChildVertex m p.1 p.2) := by
  intro v
  obtain ⟨p, hp⟩ := sgCornerVertex_surjective (m + 1) v
  rcases p with ⟨w, c⟩
  have haddr : w = Fin.cons (w 0) (sgFaceTail w) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  refine ⟨(w 0, sgCornerVertex m (sgFaceTail w, c)), ?_⟩
  calc
    sgChildVertex m (w 0) (sgCornerVertex m (sgFaceTail w, c)) =
        sgCornerVertex (m + 1)
          (Fin.cons (w 0) (sgFaceTail w), c) :=
      sgChildVertex_corner m (w 0) (sgFaceTail w) c
    _ = sgCornerVertex (m + 1) (w, c) := by rw [← haddr]
    _ = v := hp

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Two child-copy vertices are equivalent exactly when their
images in the parent gasket are the same global vertex. -/
def sgChildVertexSetoid (m : Nat) :
    Setoid (Fin 3 × SGVertex m) where
  r a b :=
    sgChildVertex m a.1 a.2 = sgChildVertex m b.1 b.2
  iseqv := by
    constructor
    · intro a
      rfl
    · intro a b h
      exact h.symm
    · intro a b c hab hbc
      exact hab.trans hbc

/-- The disjoint union of the three child vertex sets,
quotiented by their actual geometric identifications. -/
abbrev sgChildVertexQuotient (m : Nat) :=
  Quotient (sgChildVertexSetoid m)

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The quotient of the three child vertex sets maps to
the actual vertex set of the parent gasket. -/
def sgChildVertexQuotientToParent (m : Nat) :
    sgChildVertexQuotient m → SGVertex (m + 1) :=
  Quotient.lift
    (fun p : Fin 3 × SGVertex m =>
      sgChildVertex m p.1 p.2)
    (by
      intro a b hab
      exact hab)

/-- The quotient map evaluates to the corresponding
global child vertex on every representative. -/
theorem sgChildVertexQuotientToParent_mk (m : Nat)
    (p : Fin 3 × SGVertex m) :
    sgChildVertexQuotientToParent m
      (Quotient.mk (sgChildVertexSetoid m) p) =
        sgChildVertex m p.1 p.2 := by
  unfold sgChildVertexQuotientToParent
  exact Quotient.lift_mk _ _ _

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Every parent vertex is represented by a class
in the quotient of the three child vertex sets. -/
theorem sgChildVertexQuotientToParent_surjective (m : Nat) :
    Function.Surjective (sgChildVertexQuotientToParent m) := by
  intro v
  obtain ⟨p, hp⟩ := sgChildVertex_surjective_union m v
  refine ⟨Quotient.mk (sgChildVertexSetoid m) p, ?_⟩
  rw [sgChildVertexQuotientToParent_mk]
  exact hp

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The quotient map to the parent gasket is injective:
equal global vertices represent the same quotient class. -/
theorem sgChildVertexQuotientToParent_injective (m : Nat) :
    Function.Injective (sgChildVertexQuotientToParent m) := by
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  rw [sgChildVertexQuotientToParent_mk,
      sgChildVertexQuotientToParent_mk] at hab
  exact Quotient.sound hab

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The quotient of the three child vertex sets by their
geometric identifications is equivalent to the parent vertex set. -/
noncomputable def sgChildVertexQuotientEquiv (m : Nat) :
    sgChildVertexQuotient m ≃ SGVertex (m + 1) :=
  Equiv.ofBijective
    (sgChildVertexQuotientToParent m)
    ⟨sgChildVertexQuotientToParent_injective m,
      sgChildVertexQuotientToParent_surjective m⟩

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The graph energy is exactly the sum over all face-edge slots,
because the endpoint map is injective. -/
theorem sgFaceGraphEnergy_eq_edgeSlotSum (m : Nat)
    (x : SGVertex m → ℝ) :
    faceGraphEnergy x (sgFaceA m) (sgFaceB m) (sgFaceC m) =
      ∑ p : (Fin m → Fin 3) × TriangleEdge,
        (x (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).1 +
         x (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).2) ^ 2 := by
  classical
  unfold faceGraphEnergy faceGraphEdges
  have hinj :
      Set.InjOn
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m))
        (↑(Finset.univ :
          Finset ((Fin m → Fin 3) × TriangleEdge))) := by
    intro p hp q hq hpq
    exact sgFaceEdgeEndpoints_injective m hpq
  rw [Finset.sum_image hinj]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The parent graph energy is exactly the sum of the
energies of its three translated child copies. -/
theorem sgFaceGraphEnergy_eq_childSum (m : Nat)
    (x : SGVertex (m + 1) → ℝ) :
    faceGraphEnergy x
        (sgFaceA (m + 1)) (sgFaceB (m + 1)) (sgFaceC (m + 1)) =
      ∑ child : Fin 3,
        faceGraphEnergy
          (fun v : SGVertex m => x (sgChildVertex m child v))
          (sgFaceA m) (sgFaceB m) (sgFaceC m) := by
  classical
  calc
    faceGraphEnergy x
        (sgFaceA (m + 1)) (sgFaceB (m + 1)) (sgFaceC (m + 1)) =
      ∑ q : Fin 3 × ((Fin m → Fin 3) × TriangleEdge),
        (x (sgChildVertex m q.1
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            q.2).1) +
         x (sgChildVertex m q.1
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
            q.2).2)) ^ 2 := by
      rw [sgFaceGraphEnergy_eq_edgeSlotSum (m + 1) x]
      exact Fintype.sum_equiv
        (sgFaceEdgeSlotEquiv m)
        (fun s =>
          (x (faceEdgeEndpoints (sgFaceA (m + 1))
            (sgFaceB (m + 1)) (sgFaceC (m + 1)) s).1 +
           x (faceEdgeEndpoints (sgFaceA (m + 1))
            (sgFaceB (m + 1)) (sgFaceC (m + 1)) s).2) ^ 2)
        (fun q =>
          (x (sgChildVertex m q.1
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              q.2).1) +
           x (sgChildVertex m q.1
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              q.2).2)) ^ 2)
        (by
          rintro ⟨w, e⟩
          change
            (x (faceEdgeEndpoints (sgFaceA (m + 1))
              (sgFaceB (m + 1)) (sgFaceC (m + 1)) (w, e)).1 +
             x (faceEdgeEndpoints (sgFaceA (m + 1))
              (sgFaceB (m + 1)) (sgFaceC (m + 1)) (w, e)).2) ^ 2 =
            (x (sgChildVertex m (w 0)
              (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
                (sgFaceTail w, e)).1) +
             x (sgChildVertex m (w 0)
              (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
                (sgFaceTail w, e)).2)) ^ 2
          rw [sgFaceEdgeEndpoints_eq_child m w e])
    _ =
      ∑ child : Fin 3,
        ∑ p : (Fin m → Fin 3) × TriangleEdge,
          (x (sgChildVertex m child
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              p).1) +
           x (sgChildVertex m child
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)
              p).2)) ^ 2 := by
      rw [Fintype.sum_prod_type]
    _ =
      ∑ child : Fin 3,
        faceGraphEnergy
          (fun v : SGVertex m => x (sgChildVertex m child v))
          (sgFaceA m) (sgFaceB m) (sgFaceC m) := by
      apply Finset.sum_congr rfl
      intro child hchild
      symm
      exact sgFaceGraphEnergy_eq_edgeSlotSum m
        (fun v : SGVertex m => x (sgChildVertex m child v))

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- First parent midpoint: intersection of child copies 0 and 1. -/
def sgParentMidpoint01 (m : Nat) : SGVertex (m + 1) :=
  sgChildVertex m 0
    (sgCornerVertex m
      ((fun _ : Fin m => (1 : Fin 3)), .rightBase))

/-- Second parent midpoint: intersection of child copies 0 and 2. -/
def sgParentMidpoint02 (m : Nat) : SGVertex (m + 1) :=
  sgChildVertex m 0
    (sgCornerVertex m
      ((fun _ : Fin m => (2 : Fin 3)), .apex))

/-- Third parent midpoint: intersection of child copies 1 and 2. -/
def sgParentMidpoint12 (m : Nat) : SGVertex (m + 1) :=
  sgChildVertex m 1
    (sgCornerVertex m
      ((fun _ : Fin m => (2 : Fin 3)), .apex))

theorem sgParentMidpoint01_val (m : Nat) :
    (sgParentMidpoint01 m).1 = (2 ^ m, 0) := by
  change sgAddOffset m 0
    (sgFaceCornerCoords m
      ((fun _ : Fin m => (1 : Fin 3)), .rightBase)) = _
  rw [sgFaceCornerCoords_all_one_right]
  simp [sgAddOffset, sgChildOffset]

theorem sgParentMidpoint02_val (m : Nat) :
    (sgParentMidpoint02 m).1 = (0, 2 ^ m) := by
  change sgAddOffset m 0
    (sgFaceCornerCoords m
      ((fun _ : Fin m => (2 : Fin 3)), .apex)) = _
  rw [sgFaceCornerCoords_all_two_apex]
  simp [sgAddOffset, sgChildOffset]

theorem sgParentMidpoint12_val (m : Nat) :
    (sgParentMidpoint12 m).1 = (2 ^ m, 2 ^ m) := by
  change sgAddOffset m 1
    (sgFaceCornerCoords m
      ((fun _ : Fin m => (2 : Fin 3)), .apex)) = _
  rw [sgFaceCornerCoords_all_two_apex]
  norm_num [sgAddOffset, sgChildOffset]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The three pairwise intersections of child cells are distinct. -/
theorem sgParentMidpoints_pairwise_ne (m : Nat) :
    sgParentMidpoint01 m ≠ sgParentMidpoint02 m ∧
    sgParentMidpoint01 m ≠ sgParentMidpoint12 m ∧
    sgParentMidpoint02 m ≠ sgParentMidpoint12 m := by
  have hp : (0 : Nat) < (2 : Nat) ^ m := by
    positivity
  constructor
  · intro h
    have hcoord := congrArg (fun v : SGVertex (m + 1) => v.1) h
    rw [sgParentMidpoint01_val, sgParentMidpoint02_val] at hcoord
    have hzero : (2 : Nat) ^ m = 0 := by
      simpa using congrArg Prod.fst hcoord
    exact (ne_of_gt hp) hzero
  constructor
  · intro h
    have hcoord := congrArg (fun v : SGVertex (m + 1) => v.1) h
    rw [sgParentMidpoint01_val, sgParentMidpoint12_val] at hcoord
    have hzero : (0 : Nat) = (2 : Nat) ^ m := by
      simpa using congrArg Prod.snd hcoord
    exact (ne_of_gt hp).symm hzero
  · intro h
    have hcoord := congrArg (fun v : SGVertex (m + 1) => v.1) h
    rw [sgParentMidpoint02_val, sgParentMidpoint12_val] at hcoord
    have hzero : (0 : Nat) = (2 : Nat) ^ m := by
      simpa using congrArg Prod.fst hcoord
    exact (ne_of_gt hp).symm hzero
end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The finite set of parent vertices belonging to one child copy. -/
noncomputable def sgChildVertexSet (m : Nat) (child : Fin 3) :
    Finset (SGVertex (m + 1)) :=
  Finset.univ.image (sgChildVertex m child)

/-- The intersection of child copies 0 and 1 is exactly midpoint 01. -/
theorem sgChildVertexSet_inter_zero_one (m : Nat) :
    sgChildVertexSet m 0 ∩ sgChildVertexSet m 1 =
      {sgParentMidpoint01 m} := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hw0, hw1⟩
    rcases Finset.mem_image.mp hw0 with ⟨u, -, hu⟩
    rcases Finset.mem_image.mp hw1 with ⟨v, -, hv⟩
    have hEq : sgChildVertex m 0 u = sgChildVertex m 1 v :=
      hu.trans hv.symm
    have hcoords := sgChildVertex_intersection_zero_one m u v hEq
    have h0val :
        (sgChildVertex m 0 u).1 = (sgParentMidpoint01 m).1 := by
      change sgAddOffset m 0 u.1 = _
      rw [hcoords.1, sgParentMidpoint01_val]
      simp [sgAddOffset, sgChildOffset]
    have h0 : sgChildVertex m 0 u = sgParentMidpoint01 m :=
      Subtype.ext h0val
    exact Finset.mem_singleton.mpr (hu.symm.trans h0)
  · intro hw
    have hw' := Finset.mem_singleton.mp hw
    subst w
    obtain ⟨u, v, hEq⟩ := sgChildVertex_intersection_zero_one_exists m
    have hcoords := sgChildVertex_intersection_zero_one m u v hEq
    have h0val :
        (sgChildVertex m 0 u).1 = (sgParentMidpoint01 m).1 := by
      change sgAddOffset m 0 u.1 = _
      rw [hcoords.1, sgParentMidpoint01_val]
      simp [sgAddOffset, sgChildOffset]
    have h0 : sgChildVertex m 0 u = sgParentMidpoint01 m :=
      Subtype.ext h0val
    have h1 : sgChildVertex m 1 v = sgParentMidpoint01 m :=
      hEq.symm.trans h0
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, h0⟩
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, h1⟩

/-- The intersection of child copies 0 and 2 is exactly midpoint 02. -/
theorem sgChildVertexSet_inter_zero_two (m : Nat) :
    sgChildVertexSet m 0 ∩ sgChildVertexSet m 2 =
      {sgParentMidpoint02 m} := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hw0, hw2⟩
    rcases Finset.mem_image.mp hw0 with ⟨u, -, hu⟩
    rcases Finset.mem_image.mp hw2 with ⟨v, -, hv⟩
    have hEq : sgChildVertex m 0 u = sgChildVertex m 2 v :=
      hu.trans hv.symm
    have hcoords := sgChildVertex_intersection_zero_two m u v hEq
    have h0val :
        (sgChildVertex m 0 u).1 = (sgParentMidpoint02 m).1 := by
      change sgAddOffset m 0 u.1 = _
      rw [hcoords.1, sgParentMidpoint02_val]
      simp [sgAddOffset, sgChildOffset]
    have h0 : sgChildVertex m 0 u = sgParentMidpoint02 m :=
      Subtype.ext h0val
    exact Finset.mem_singleton.mpr (hu.symm.trans h0)
  · intro hw
    have hw' := Finset.mem_singleton.mp hw
    subst w
    obtain ⟨u, v, hEq⟩ := sgChildVertex_intersection_zero_two_exists m
    have hcoords := sgChildVertex_intersection_zero_two m u v hEq
    have h0val :
        (sgChildVertex m 0 u).1 = (sgParentMidpoint02 m).1 := by
      change sgAddOffset m 0 u.1 = _
      rw [hcoords.1, sgParentMidpoint02_val]
      simp [sgAddOffset, sgChildOffset]
    have h0 : sgChildVertex m 0 u = sgParentMidpoint02 m :=
      Subtype.ext h0val
    have h2 : sgChildVertex m 2 v = sgParentMidpoint02 m :=
      hEq.symm.trans h0
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, h0⟩
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, h2⟩

/-- The intersection of child copies 1 and 2 is exactly midpoint 12. -/
theorem sgChildVertexSet_inter_one_two (m : Nat) :
    sgChildVertexSet m 1 ∩ sgChildVertexSet m 2 =
      {sgParentMidpoint12 m} := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hw1, hw2⟩
    rcases Finset.mem_image.mp hw1 with ⟨u, -, hu⟩
    rcases Finset.mem_image.mp hw2 with ⟨v, -, hv⟩
    have hEq : sgChildVertex m 1 u = sgChildVertex m 2 v :=
      hu.trans hv.symm
    have hcoords := sgChildVertex_intersection_one_two m u v hEq
    have h1val :
        (sgChildVertex m 1 u).1 = (sgParentMidpoint12 m).1 := by
      change sgAddOffset m 1 u.1 = _
      rw [hcoords.1, sgParentMidpoint12_val]
      simp [sgAddOffset, sgChildOffset]
    have h1 : sgChildVertex m 1 u = sgParentMidpoint12 m :=
      Subtype.ext h1val
    exact Finset.mem_singleton.mpr (hu.symm.trans h1)
  · intro hw
    have hw' := Finset.mem_singleton.mp hw
    subst w
    obtain ⟨u, v, hEq⟩ := sgChildVertex_intersection_one_two_exists m
    have hcoords := sgChildVertex_intersection_one_two m u v hEq
    have h1val :
        (sgChildVertex m 1 u).1 = (sgParentMidpoint12 m).1 := by
      change sgAddOffset m 1 u.1 = _
      rw [hcoords.1, sgParentMidpoint12_val]
      simp [sgAddOffset, sgChildOffset]
    have h1 : sgChildVertex m 1 u = sgParentMidpoint12 m :=
      Subtype.ext h1val
    have h2 : sgChildVertex m 2 v = sgParentMidpoint12 m :=
      hEq.symm.trans h1
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, h1⟩
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, h2⟩

/-- The three child vertex sets cover the entire parent vertex set. -/
theorem sgChildVertexSet_union (m : Nat) :
    sgChildVertexSet m 0 ∪
      sgChildVertexSet m 1 ∪
      sgChildVertexSet m 2 = Finset.univ := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro _
    simp
  · intro _
    obtain ⟨p, hp⟩ := sgChildVertex_surjective_union m w
    rcases p with ⟨i, v⟩
    fin_cases i
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr
            ⟨v, Finset.mem_univ v, hp⟩))))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr
            ⟨v, Finset.mem_univ v, hp⟩))))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr
          ⟨v, Finset.mem_univ v, hp⟩))

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The sum of squared values over the three child copies equals
the parent mass plus the three midpoint contributions. -/
theorem sgChildVertex_mass_identity (m : Nat)
    (x : SGVertex (m + 1) → ℝ) :
    (∑ v : SGVertex m, x (sgChildVertex m 0 v) ^ 2) +
      (∑ v : SGVertex m, x (sgChildVertex m 1 v) ^ 2) +
      (∑ v : SGVertex m, x (sgChildVertex m 2 v) ^ 2) =
    (∑ w : SGVertex (m + 1), x w ^ 2) +
      x (sgParentMidpoint01 m) ^ 2 +
      x (sgParentMidpoint02 m) ^ 2 +
      x (sgParentMidpoint12 m) ^ 2 := by
  classical
  let f : SGVertex (m + 1) → ℝ := fun w => x w ^ 2
  let A : Finset (SGVertex (m + 1)) := sgChildVertexSet m 0
  let B : Finset (SGVertex (m + 1)) := sgChildVertexSet m 1
  let C : Finset (SGVertex (m + 1)) := sgChildVertexSet m 2

  have hImage (i : Fin 3) :
      (∑ v : SGVertex m, f (sgChildVertex m i v)) =
        (∑ w ∈ sgChildVertexSet m i, f w) := by
    dsimp [sgChildVertexSet]
    have hi : Set.InjOn (sgChildVertex m i)
        (↑(Finset.univ : Finset (SGVertex m))) := by
      intro u hu v hv huv
      exact sgChildVertex_injective m i huv
    rw [Finset.sum_image hi]

  have hABset : A ∩ B = {sgParentMidpoint01 m} := by
    simpa [A, B] using sgChildVertexSet_inter_zero_one m

  have hACset : A ∩ C = {sgParentMidpoint02 m} := by
    simpa [A, C] using sgChildVertexSet_inter_zero_two m

  have hBCset : B ∩ C = {sgParentMidpoint12 m} := by
    simpa [B, C] using sgChildVertexSet_inter_one_two m

  have hABCset : (A ∪ B) ∩ C =
      {sgParentMidpoint02 m} ∪ {sgParentMidpoint12 m} := by
    calc
      (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
        ext w
        simp only [Finset.mem_inter, Finset.mem_union]
        tauto
      _ = _ := by rw [hACset, hBCset]

  have hmid := sgParentMidpoints_pairwise_ne m

  have hDisjoint :
      Disjoint
        ({sgParentMidpoint02 m} : Finset (SGVertex (m + 1)))
        {sgParentMidpoint12 m} := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact hmid.2.2
      ((Finset.mem_singleton.mp hw).symm.trans
        (Finset.mem_singleton.mp hw'))

  have hABsum :
      (∑ w ∈ A ∪ B, f w) + f (sgParentMidpoint01 m) =
        (∑ w ∈ A, f w) + (∑ w ∈ B, f w) := by
    have h := Finset.sum_union_inter
      (s₁ := A) (s₂ := B) (f := f)
    rw [hABset] at h
    simpa using h

  have hABCsum :
      (∑ w ∈ (A ∪ B) ∪ C, f w) +
          (f (sgParentMidpoint02 m) + f (sgParentMidpoint12 m)) =
        (∑ w ∈ A ∪ B, f w) + (∑ w ∈ C, f w) := by
    have h := Finset.sum_union_inter
      (s₁ := A ∪ B) (s₂ := C) (f := f)
    rw [hABCset, Finset.sum_union hDisjoint] at h
    simpa using h

  have hUnion : (A ∪ B) ∪ C =
      (Finset.univ : Finset (SGVertex (m + 1))) := by
    simpa [A, B, C] using sgChildVertexSet_union m

  have hParentSum :
      (∑ w ∈ (A ∪ B) ∪ C, f w) =
        (∑ w : SGVertex (m + 1), f w) := by
    rw [hUnion]

  have hImageSums :
      (∑ v : SGVertex m, f (sgChildVertex m 0 v)) +
        (∑ v : SGVertex m, f (sgChildVertex m 1 v)) +
        (∑ v : SGVertex m, f (sgChildVertex m 2 v)) =
      (∑ w ∈ A, f w) + (∑ w ∈ B, f w) + (∑ w ∈ C, f w) := by
    rw [hImage 0, hImage 1, hImage 2]

  have hSetSums :
      (∑ w ∈ A, f w) + (∑ w ∈ B, f w) + (∑ w ∈ C, f w) =
        (∑ w ∈ (A ∪ B) ∪ C, f w) +
          f (sgParentMidpoint01 m) +
          f (sgParentMidpoint02 m) +
          f (sgParentMidpoint12 m) := by
    linarith [hABsum, hABCsum]

  calc
    (∑ v : SGVertex m, f (sgChildVertex m 0 v)) +
        (∑ v : SGVertex m, f (sgChildVertex m 1 v)) +
        (∑ v : SGVertex m, f (sgChildVertex m 2 v))
        =
      (∑ w ∈ A, f w) + (∑ w ∈ B, f w) + (∑ w ∈ C, f w) :=
        hImageSums
    _ =
      (∑ w ∈ (A ∪ B) ∪ C, f w) +
        f (sgParentMidpoint01 m) +
        f (sgParentMidpoint02 m) +
        f (sgParentMidpoint12 m) :=
        hSetSums
    _ =
      (∑ w : SGVertex (m + 1), f w) +
        f (sgParentMidpoint01 m) +
        f (sgParentMidpoint02 m) +
        f (sgParentMidpoint12 m) := by
          rw [hParentSum]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- Exact mass decomposition across the three child copies,
including the three shared midpoint contributions. -/
theorem sgChildVertex_mass_identity_check (m : Nat)
    (x : SGVertex (m + 1) → ℝ) :
    (∑ v : SGVertex m, x (sgChildVertex m 0 v) ^ 2) +
      (∑ v : SGVertex m, x (sgChildVertex m 1 v) ^ 2) +
      (∑ v : SGVertex m, x (sgChildVertex m 2 v) ^ 2) =
    (∑ w : SGVertex (m + 1), x w ^ 2) +
      x (sgParentMidpoint01 m) ^ 2 +
      x (sgParentMidpoint02 m) ^ 2 +
      x (sgParentMidpoint12 m) ^ 2 := by
  classical
  let f : SGVertex (m + 1) → ℝ := fun w => x w ^ 2
  let A : Finset (SGVertex (m + 1)) := sgChildVertexSet m 0
  let B : Finset (SGVertex (m + 1)) := sgChildVertexSet m 1
  let C : Finset (SGVertex (m + 1)) := sgChildVertexSet m 2

  have hImage (i : Fin 3) :
      (∑ v : SGVertex m, f (sgChildVertex m i v)) =
        (∑ w ∈ sgChildVertexSet m i, f w) := by
    dsimp [sgChildVertexSet]
    have hi : Set.InjOn (sgChildVertex m i)
        (↑(Finset.univ : Finset (SGVertex m))) := by
      intro u hu v hv huv
      exact sgChildVertex_injective m i huv
    rw [Finset.sum_image hi]

  have hABset : A ∩ B = {sgParentMidpoint01 m} := by
    simpa [A, B] using sgChildVertexSet_inter_zero_one m
  have hACset : A ∩ C = {sgParentMidpoint02 m} := by
    simpa [A, C] using sgChildVertexSet_inter_zero_two m
  have hBCset : B ∩ C = {sgParentMidpoint12 m} := by
    simpa [B, C] using sgChildVertexSet_inter_one_two m

  have hABCset : (A ∪ B) ∩ C =
      {sgParentMidpoint02 m} ∪ {sgParentMidpoint12 m} := by
    calc
      (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
        ext w
        simp only [Finset.mem_inter, Finset.mem_union]
        tauto
      _ = _ := by rw [hACset, hBCset]

  have hmid := sgParentMidpoints_pairwise_ne m
  have hDisjoint :
      Disjoint
        ({sgParentMidpoint02 m} : Finset (SGVertex (m + 1)))
        {sgParentMidpoint12 m} := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact hmid.2.2
      ((Finset.mem_singleton.mp hw).symm.trans
        (Finset.mem_singleton.mp hw'))

  have hABsum :
      (∑ w ∈ A ∪ B, f w) + f (sgParentMidpoint01 m) =
        (∑ w ∈ A, f w) + (∑ w ∈ B, f w) := by
    have h := Finset.sum_union_inter
      (s₁ := A) (s₂ := B) (f := f)
    rw [hABset] at h
    simpa using h

  have hABCsum :
      (∑ w ∈ (A ∪ B) ∪ C, f w) +
          (f (sgParentMidpoint02 m) + f (sgParentMidpoint12 m)) =
        (∑ w ∈ A ∪ B, f w) + (∑ w ∈ C, f w) := by
    have h := Finset.sum_union_inter
      (s₁ := A ∪ B) (s₂ := C) (f := f)
    rw [hABCset, Finset.sum_union hDisjoint] at h
    simpa using h

  have hUnion : (A ∪ B) ∪ C =
      (Finset.univ : Finset (SGVertex (m + 1))) := by
    simpa [A, B, C] using sgChildVertexSet_union m

  have hParentSum :
      (∑ w ∈ (A ∪ B) ∪ C, f w) =
        (∑ w : SGVertex (m + 1), f w) := by
    simp [hUnion]

  have hImageSums :
      (∑ v : SGVertex m, f (sgChildVertex m 0 v)) +
        (∑ v : SGVertex m, f (sgChildVertex m 1 v)) +
        (∑ v : SGVertex m, f (sgChildVertex m 2 v)) =
      (∑ w ∈ A, f w) + (∑ w ∈ B, f w) + (∑ w ∈ C, f w) := by
    dsimp [A, B, C]
    rw [← hImage 0, ← hImage 1, ← hImage 2]

  have hSetSums :
      (∑ w ∈ A, f w) + (∑ w ∈ B, f w) + (∑ w ∈ C, f w) =
        (∑ w ∈ (A ∪ B) ∪ C, f w) +
          f (sgParentMidpoint01 m) +
          f (sgParentMidpoint02 m) +
          f (sgParentMidpoint12 m) := by
    calc
      _ = ((∑ w ∈ A ∪ B, f w) + f (sgParentMidpoint01 m)) +
            (∑ w ∈ C, f w) := by
              rw [← hABsum]
      _ = ((∑ w ∈ A ∪ B, f w) + (∑ w ∈ C, f w)) +
            f (sgParentMidpoint01 m) := by ring
      _ = ((∑ w ∈ (A ∪ B) ∪ C, f w) +
            (f (sgParentMidpoint02 m) + f (sgParentMidpoint12 m))) +
            f (sgParentMidpoint01 m) := by
              rw [← hABCsum]
      _ = (∑ w ∈ (A ∪ B) ∪ C, f w) +
            f (sgParentMidpoint01 m) +
            f (sgParentMidpoint02 m) +
            f (sgParentMidpoint12 m) := by ring

  calc
    _ = (∑ w ∈ A, f w) + (∑ w ∈ B, f w) +
          (∑ w ∈ C, f w) := hImageSums
    _ = (∑ w ∈ (A ∪ B) ∪ C, f w) +
          f (sgParentMidpoint01 m) +
          f (sgParentMidpoint02 m) +
          f (sgParentMidpoint12 m) := hSetSums
    _ = (∑ w : SGVertex (m + 1), f w) +
          f (sgParentMidpoint01 m) +
          f (sgParentMidpoint02 m) +
          f (sgParentMidpoint12 m) := by
            rw [hParentSum]

end PhiGenesis.SpectralGap

namespace PhiGenesis.SpectralGap

/-- Exact decomposition of the shifted graph energy into the three shifted child energies and the midpoint mass correction. -/
theorem sgFaceGraphShiftedEnergy_eq_childShifted
    (m : Nat) (lambda : ℝ) (x : SGVertex (m + 1) → ℝ) :
    faceGraphEnergy x (sgFaceA (m + 1))
        (sgFaceB (m + 1)) (sgFaceC (m + 1)) -
      lambda * (∑ w : SGVertex (m + 1), x w ^ 2) =
    (faceGraphEnergy
        (fun v : SGVertex m => x (sgChildVertex m 0 v))
        (sgFaceA m) (sgFaceB m) (sgFaceC m) -
      lambda * (∑ v : SGVertex m,
        x (sgChildVertex m 0 v) ^ 2)) +
    (faceGraphEnergy
        (fun v : SGVertex m => x (sgChildVertex m 1 v))
        (sgFaceA m) (sgFaceB m) (sgFaceC m) -
      lambda * (∑ v : SGVertex m,
        x (sgChildVertex m 1 v) ^ 2)) +
    (faceGraphEnergy
        (fun v : SGVertex m => x (sgChildVertex m 2 v))
        (sgFaceA m) (sgFaceB m) (sgFaceC m) -
      lambda * (∑ v : SGVertex m,
        x (sgChildVertex m 2 v) ^ 2)) +
    lambda * (x (sgParentMidpoint01 m) ^ 2 +
      x (sgParentMidpoint02 m) ^ 2 +
      x (sgParentMidpoint12 m) ^ 2) := by
  classical
  have hsum3 (g : Fin 3 → ℝ) :
      (∑ i : Fin 3, g i) = g 0 + g 1 + g 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h1 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
    have h2 : Fin.succ (Fin.succ (0 : Fin 1)) = (2 : Fin 3) := by decide
    rw [h1, h2, Fin.sum_univ_zero]
    ring

  let E0 := faceGraphEnergy
    (fun v : SGVertex m => x (sgChildVertex m 0 v))
    (sgFaceA m) (sgFaceB m) (sgFaceC m)
  let E1 := faceGraphEnergy
    (fun v : SGVertex m => x (sgChildVertex m 1 v))
    (sgFaceA m) (sgFaceB m) (sgFaceC m)
  let E2 := faceGraphEnergy
    (fun v : SGVertex m => x (sgChildVertex m 2 v))
    (sgFaceA m) (sgFaceB m) (sgFaceC m)

  let M0 := ∑ v : SGVertex m, x (sgChildVertex m 0 v) ^ 2
  let M1 := ∑ v : SGVertex m, x (sgChildVertex m 1 v) ^ 2
  let M2 := ∑ v : SGVertex m, x (sgChildVertex m 2 v) ^ 2
  let Mp := ∑ w : SGVertex (m + 1), x w ^ 2
  let D := x (sgParentMidpoint01 m) ^ 2 +
    x (sgParentMidpoint02 m) ^ 2 +
    x (sgParentMidpoint12 m) ^ 2

  have hE :
      faceGraphEnergy x (sgFaceA (m + 1))
          (sgFaceB (m + 1)) (sgFaceC (m + 1)) =
        E0 + E1 + E2 := by
    have h := sgFaceGraphEnergy_eq_childSum m x
    rw [hsum3] at h
    simpa [E0, E1, E2] using h

  have hM0 :
      M0 + M1 + M2 =
        Mp + x (sgParentMidpoint01 m) ^ 2 +
          x (sgParentMidpoint02 m) ^ 2 +
          x (sgParentMidpoint12 m) ^ 2 := by
    simpa [M0, M1, M2, Mp] using
      sgChildVertex_mass_identity_check m x

  have hM : M0 + M1 + M2 = Mp + D := by
    calc
      _ = Mp + x (sgParentMidpoint01 m) ^ 2 +
            x (sgParentMidpoint02 m) ^ 2 +
            x (sgParentMidpoint12 m) ^ 2 := hM0
      _ = Mp + D := by
        simp only [D]
        ring

  change
    faceGraphEnergy x (sgFaceA (m + 1))
        (sgFaceB (m + 1)) (sgFaceC (m + 1)) -
      lambda * Mp =
    (E0 - lambda * M0) + (E1 - lambda * M1) +
      (E2 - lambda * M2) + lambda * D

  calc
    _ = (E0 + E1 + E2) - lambda * Mp := by rw [hE]
    _ = (E0 + E1 + E2) -
          lambda * (M0 + M1 + M2) + lambda * D := by
          rw [hM]
          ring
    _ = (E0 - lambda * M0) + (E1 - lambda * M1) +
          (E2 - lambda * M2) + lambda * D := by ring


end PhiGenesis.SpectralGap

namespace PhiGenesis.SpectralGap

/-- Entrywise gauge relation between the signless and signed matrices. -/
theorem sgSignlessLaplacianMatrix_entry_gauge (m : Nat)
    (u v : SGVertex m) :
    sgSignedLaplacianMatrix m u v =
      sgVertexGauge u * sgSignlessLaplacianMatrix m u v *
        sgVertexGauge v := by
  have h := congrArg
    (fun M : Matrix (SGVertex m) (SGVertex m) ℝ => M u v)
    (sgSignedLaplacianMatrix_eq_gauge_conj m)
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using h

theorem sgSignlessLaplacianMatrix_quadraticForm (m : Nat)
    (x : SGVertex m → ℝ) :
    (∑ u : SGVertex m, x u *
      ∑ v : SGVertex m, sgSignlessLaplacianMatrix m u v * x v) =
      faceGraphEnergy x (sgFaceA m) (sgFaceB m) (sgFaceC m) := by
  classical
  let g : SGVertex m → ℝ := sgVertexGauge
  let y : SGVertex m → ℝ := fun v => g v * x v

  have hQ (u v : SGVertex m) :
      sgSignlessLaplacianMatrix m u v =
        sgVertexGauge u * sgSignedLaplacianMatrix m u v *
          sgVertexGauge v := by
    have hL := sgSignlessLaplacianMatrix_entry_gauge m u v
    have hu : sgVertexGauge u * sgVertexGauge u = 1 := by
      nlinarith [sgVertexGauge_sq u]
    have hv : sgVertexGauge v * sgVertexGauge v = 1 := by
      nlinarith [sgVertexGauge_sq v]
    calc
      sgSignlessLaplacianMatrix m u v =
          (sgVertexGauge u * sgVertexGauge u) *
            sgSignlessLaplacianMatrix m u v *
            (sgVertexGauge v * sgVertexGauge v) := by
              rw [hu, hv]
              ring
      _ = sgVertexGauge u *
            (sgVertexGauge u * sgSignlessLaplacianMatrix m u v *
              sgVertexGauge v) * sgVertexGauge v := by ring
      _ = sgVertexGauge u * sgSignedLaplacianMatrix m u v *
            sgVertexGauge v := by rw [← hL]

  have hrow (u : SGVertex m) :
      x u * (∑ v : SGVertex m,
        sgSignlessLaplacianMatrix m u v * x v) =
      y u * (∑ v : SGVertex m,
        sgSignedLaplacianMatrix m u v * y v) := by
    calc
      _ = ∑ v : SGVertex m,
          x u * (sgSignlessLaplacianMatrix m u v * x v) := by
            rw [← Finset.mul_sum]
      _ = ∑ v : SGVertex m,
          y u * (sgSignedLaplacianMatrix m u v * y v) := by
            apply Finset.sum_congr rfl
            intro v hv
            dsimp [y, g]
            rw [hQ u v]
            ring
      _ = _ := by rw [Finset.mul_sum]

  calc
    (∑ u : SGVertex m, x u *
        ∑ v : SGVertex m, sgSignlessLaplacianMatrix m u v * x v) =
      ∑ u : SGVertex m, y u *
        ∑ v : SGVertex m, sgSignedLaplacianMatrix m u v * y v := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hrow u
    _ = sgSignedGraphEnergy m y :=
          sgSignedLaplacianMatrix_quadraticForm m y
    _ = faceGraphEnergy x
          (sgFaceA m) (sgFaceB m) (sgFaceC m) := by
          rw [sgSignedGraphEnergy_eq_gauged]
          congr 1
          funext v
          dsimp [y, g]
          calc
            sgVertexGauge v * (sgVertexGauge v * x v) =
                (sgVertexGauge v) ^ 2 * x v := by ring
            _ = x v := by rw [sgVertexGauge_sq]; ring


end PhiGenesis.SpectralGap

namespace PhiGenesis.SpectralGap

/-- The quadratic form of the shifted signless matrix is the graph energy minus lambda times the vertex mass. -/
theorem sgSignlessShiftedMatrix_quadraticForm
    (m : Nat) (lambda : ℝ) (x : SGVertex m → ℝ) :
    (∑ u : SGVertex m, x u *
      ∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          x v) =
      faceGraphEnergy x (sgFaceA m) (sgFaceB m) (sgFaceC m) -
        lambda * (∑ u : SGVertex m, x u ^ 2) := by
  classical
  have hEntry (u v : SGVertex m) :
      (sgSignlessLaplacianMatrix m -
        lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v =
        sgSignlessLaplacianMatrix m u v -
          lambda * (if u = v then (1 : ℝ) else 0) := by
    simp [Matrix.sub_apply, Matrix.one_apply]

  have hDiag (u : SGVertex m) :
      (∑ v : SGVertex m,
        (if u = v then (1 : ℝ) else 0) * x v) = x u := by
    simp

  have hRow (u : SGVertex m) :
      (∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          x v) =
      (∑ v : SGVertex m, sgSignlessLaplacianMatrix m u v * x v) -
        lambda * x u := by
    calc
      _ = ∑ v : SGVertex m,
          (sgSignlessLaplacianMatrix m u v -
            lambda * (if u = v then (1 : ℝ) else 0)) * x v := by
              apply Finset.sum_congr rfl
              intro v hv
              rw [hEntry]
      _ = ∑ v : SGVertex m,
          (sgSignlessLaplacianMatrix m u v * x v -
            lambda * ((if u = v then (1 : ℝ) else 0) * x v)) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
      _ = (∑ v : SGVertex m,
            sgSignlessLaplacianMatrix m u v * x v) -
          (∑ v : SGVertex m,
            lambda * ((if u = v then (1 : ℝ) else 0) * x v)) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ v : SGVertex m,
            sgSignlessLaplacianMatrix m u v * x v) -
          lambda * (∑ v : SGVertex m,
            (if u = v then (1 : ℝ) else 0) * x v) := by
              rw [← Finset.mul_sum]
      _ = _ := by rw [hDiag]

  calc
    _ = ∑ u : SGVertex m,
          (x u * (∑ v : SGVertex m,
            sgSignlessLaplacianMatrix m u v * x v) -
            x u * (lambda * x u)) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [hRow]
              ring
    _ = (∑ u : SGVertex m,
          x u * (∑ v : SGVertex m,
            sgSignlessLaplacianMatrix m u v * x v)) -
        (∑ u : SGVertex m, x u * (lambda * x u)) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ u : SGVertex m,
          x u * (∑ v : SGVertex m,
            sgSignlessLaplacianMatrix m u v * x v)) -
        lambda * (∑ u : SGVertex m, x u ^ 2) := by
          congr 1
          calc
            (∑ u : SGVertex m, x u * (lambda * x u)) =
                ∑ u : SGVertex m, lambda * (x u) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  ring
            _ = lambda * (∑ u : SGVertex m, x u ^ 2) := by
                  rw [Finset.mul_sum]
    _ = _ := by
          rw [sgSignlessLaplacianMatrix_quadraticForm]


end PhiGenesis.SpectralGap

namespace PhiGenesis.SpectralGap

/-- The shifted signless matrix quadratic form decomposes over the three child copies, with the shared-midpoint correction. -/
theorem sgSignlessShiftedMatrix_childDecomposition
    (m : Nat) (lambda : ℝ)
    (x : SGVertex (m + 1) → ℝ) :
    (∑ u : SGVertex (m + 1), x u *
      ∑ v : SGVertex (m + 1),
        (sgSignlessLaplacianMatrix (m + 1) -
          lambda • (1 : Matrix (SGVertex (m + 1))
            (SGVertex (m + 1)) ℝ)) u v * x v) =
    (∑ u : SGVertex m, x (sgChildVertex m 0 u) *
      ∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          x (sgChildVertex m 0 v)) +
    (∑ u : SGVertex m, x (sgChildVertex m 1 u) *
      ∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          x (sgChildVertex m 1 v)) +
    (∑ u : SGVertex m, x (sgChildVertex m 2 u) *
      ∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          x (sgChildVertex m 2 v)) +
    lambda * (x (sgParentMidpoint01 m) ^ 2 +
      x (sgParentMidpoint02 m) ^ 2 +
      x (sgParentMidpoint12 m) ^ 2) := by
  simpa only [← sgSignlessShiftedMatrix_quadraticForm] using
    sgFaceGraphShiftedEnergy_eq_childShifted m lambda x


end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The three outer corners of the parent gasket. -/
def sgParentOuterCorner0 (m : Nat) : SGVertex (m + 1) :=
  sgChildVertex m 0
    (sgCornerVertex m
      ((fun _ : Fin m => (0 : Fin 3)), .leftBase))

def sgParentOuterCorner1 (m : Nat) : SGVertex (m + 1) :=
  sgChildVertex m 1
    (sgCornerVertex m
      ((fun _ : Fin m => (1 : Fin 3)), .rightBase))

def sgParentOuterCorner2 (m : Nat) : SGVertex (m + 1) :=
  sgChildVertex m 2
    (sgCornerVertex m
      ((fun _ : Fin m => (2 : Fin 3)), .apex))

theorem sgParentOuterCorner0_val (m : Nat) :
    (sgParentOuterCorner0 m).1 = (0, 0) := by
  change sgAddOffset m 0
    (sgFaceCornerCoords m
      ((fun _ : Fin m => (0 : Fin 3)), .leftBase)) = _
  rw [sgFaceCornerCoords_all_zero_left]
  simp [sgAddOffset, sgChildOffset]

theorem sgParentOuterCorner1_val (m : Nat) :
    (sgParentOuterCorner1 m).1 = (2 ^ (m + 1), 0) := by
  change sgAddOffset m 1
    (sgFaceCornerCoords m
      ((fun _ : Fin m => (1 : Fin 3)), .rightBase)) = _
  rw [sgFaceCornerCoords_all_one_right]
  simp [sgAddOffset, sgChildOffset, pow_succ, Nat.mul_two]

theorem sgParentOuterCorner2_val (m : Nat) :
    (sgParentOuterCorner2 m).1 = (0, 2 ^ (m + 1)) := by
  change sgAddOffset m 2
    (sgFaceCornerCoords m
      ((fun _ : Fin m => (2 : Fin 3)), .apex)) = _
  rw [sgFaceCornerCoords_all_two_apex]
  simp [sgAddOffset, sgChildOffset, pow_succ, Nat.mul_two]

/-- Fixed ordering: outer corners 0,1,2, then shared midpoints 01,02,12. -/
def sgParentBoundaryVertex (m : Nat) : Fin 6 → SGVertex (m + 1)
  | 0 => sgParentOuterCorner0 m
  | 1 => sgParentOuterCorner1 m
  | 2 => sgParentOuterCorner2 m
  | 3 => sgParentMidpoint01 m
  | 4 => sgParentMidpoint02 m
  | 5 => sgParentMidpoint12 m

theorem sgParentBoundaryVertex_val (m : Nat) (i : Fin 6) :
    (sgParentBoundaryVertex m i).1 =
      match i with
      | 0 => (0, 0)
      | 1 => (2 ^ (m + 1), 0)
      | 2 => (0, 2 ^ (m + 1))
      | 3 => (2 ^ m, 0)
      | 4 => (0, 2 ^ m)
      | 5 => (2 ^ m, 2 ^ m) := by
  fin_cases i
  · exact sgParentOuterCorner0_val m
  · exact sgParentOuterCorner1_val m
  · exact sgParentOuterCorner2_val m
  · exact sgParentMidpoint01_val m
  · exact sgParentMidpoint02_val m
  · exact sgParentMidpoint12_val m

/-- The six retained boundary vertices are pairwise distinct. -/
theorem sgParentBoundaryVertex_injective (m : Nat) :
    Function.Injective (sgParentBoundaryVertex m) := by
  intro i j hij
  have hcoord :=
    congrArg (fun v : SGVertex (m + 1) => v.1) hij
  rw [sgParentBoundaryVertex_val m i,
      sgParentBoundaryVertex_val m j] at hcoord
  have hp : 0 < 2 ^ m := by
    positivity
  have hside : 2 ^ m < 2 ^ (m + 1) := by
    rw [pow_succ]
    nlinarith
  fin_cases i <;> fin_cases j <;>
    simp_all <;> omega

/-- The finite set of six retained parent boundary vertices. -/
noncomputable def sgParentBoundarySet (m : Nat) :
    Finset (SGVertex (m + 1)) :=
  Finset.univ.image (sgParentBoundaryVertex m)

/-- All vertices not belonging to the six-point retained boundary. -/
noncomputable def sgParentInteriorSet (m : Nat) :
    Finset (SGVertex (m + 1)) :=
  Finset.univ \ sgParentBoundarySet m

theorem sgParentInteriorSet_mem_iff (m : Nat)
    (v : SGVertex (m + 1)) :
    v ∈ sgParentInteriorSet m ↔
      v ∉ sgParentBoundarySet m := by
  simp [sgParentInteriorSet]

end PhiGenesis.SpectralGap


namespace PhiGenesis.SpectralGap

/-- The three outer corners of a level-m child gasket. -/
def sgLevelOuterCorner (m : Nat) : TriangleCorner → SGVertex m
  | .leftBase =>
      sgCornerVertex m ((fun _ : Fin m => (0 : Fin 3)), .leftBase)
  | .rightBase =>
      sgCornerVertex m ((fun _ : Fin m => (1 : Fin 3)), .rightBase)
  | .apex =>
      sgCornerVertex m ((fun _ : Fin m => (2 : Fin 3)), .apex)

/-- Global boundary index of a corner of one of the three children.

Child 0 uses indices (0,3,4), child 1 uses (3,1,5),
and child 2 uses (4,5,2). -/
def sgChildCornerBoundaryIndex
    (child : Fin 3) (corner : TriangleCorner) : Fin 6 :=
  if child = (0 : Fin 3) then
    match corner with
    | .leftBase => 0
    | .rightBase => 3
    | .apex => 4
  else if child = (1 : Fin 3) then
    match corner with
    | .leftBase => 3
    | .rightBase => 1
    | .apex => 5
  else
    match corner with
    | .leftBase => 4
    | .rightBase => 5
    | .apex => 2

/-- Child 1's left corner is the shared midpoint 01. -/
theorem sgChildOneLeft_eq_midpoint01 (m : Nat) :
    sgChildVertex m 1 (sgLevelOuterCorner m .leftBase) =
      sgParentMidpoint01 m := by
  apply Subtype.ext
  change
    sgAddOffset m 1
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (0 : Fin 3)), .leftBase)) =
    sgAddOffset m 0
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (1 : Fin 3)), .rightBase))
  rw [sgFaceCornerCoords_all_zero_left,
      sgFaceCornerCoords_all_one_right]
  simp [sgAddOffset, sgChildOffset]

/-- Child 2's left corner is the shared midpoint 02. -/
theorem sgChildTwoLeft_eq_midpoint02 (m : Nat) :
    sgChildVertex m 2 (sgLevelOuterCorner m .leftBase) =
      sgParentMidpoint02 m := by
  apply Subtype.ext
  change
    sgAddOffset m 2
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (0 : Fin 3)), .leftBase)) =
    sgAddOffset m 0
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (2 : Fin 3)), .apex))
  rw [sgFaceCornerCoords_all_zero_left,
      sgFaceCornerCoords_all_two_apex]
  simp [sgAddOffset, sgChildOffset]

/-- Child 2's right corner is the shared midpoint 12. -/
theorem sgChildTwoRight_eq_midpoint12 (m : Nat) :
    sgChildVertex m 2 (sgLevelOuterCorner m .rightBase) =
      sgParentMidpoint12 m := by
  apply Subtype.ext
  change
    sgAddOffset m 2
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (1 : Fin 3)), .rightBase)) =
    sgAddOffset m 1
      (sgFaceCornerCoords m
        ((fun _ : Fin m => (2 : Fin 3)), .apex))
  rw [sgFaceCornerCoords_all_one_right,
      sgFaceCornerCoords_all_two_apex]
  simp [sgAddOffset, sgChildOffset]

/-- Every child corner is exactly the corresponding global
outer corner or shared midpoint of the parent. -/
theorem sgChildCorner_maps_parentBoundary (m : Nat)
    (child : Fin 3) (corner : TriangleCorner) :
    sgChildVertex m child (sgLevelOuterCorner m corner) =
      sgParentBoundaryVertex m
        (sgChildCornerBoundaryIndex child corner) := by
  fin_cases child
  · cases corner <;>
      simp [sgChildCornerBoundaryIndex, sgParentBoundaryVertex,
        sgLevelOuterCorner, sgParentOuterCorner0,
        sgParentMidpoint01, sgParentMidpoint02]
  · cases corner with
    | leftBase =>
        simpa [sgChildCornerBoundaryIndex, sgParentBoundaryVertex] using
          sgChildOneLeft_eq_midpoint01 m
    | rightBase =>
        simp [sgChildCornerBoundaryIndex, sgParentBoundaryVertex,
          sgLevelOuterCorner, sgParentOuterCorner1]
    | apex =>
        simp [sgChildCornerBoundaryIndex, sgParentBoundaryVertex,
          sgLevelOuterCorner, sgParentMidpoint12]
  · cases corner with
    | leftBase =>
        simpa [sgChildCornerBoundaryIndex, sgParentBoundaryVertex] using
          sgChildTwoLeft_eq_midpoint02 m
    | rightBase =>
        simpa [sgChildCornerBoundaryIndex, sgParentBoundaryVertex] using
          sgChildTwoRight_eq_midpoint12 m
    | apex =>
        simp [sgChildCornerBoundaryIndex, sgParentBoundaryVertex,
          sgLevelOuterCorner, sgParentOuterCorner2]

/-- Restriction of a parent vertex function to its six boundary coordinates. -/
def sgParentBoundaryRestriction (m : Nat)
    (x : SGVertex (m + 1) → ℝ) : Fin 6 → ℝ :=
  fun i => x (sgParentBoundaryVertex m i)

/-- Values at child corners agree with the corresponding
coordinates of the parent boundary restriction. -/
theorem sgChildCornerValue_eq_parentBoundary (m : Nat)
    (x : SGVertex (m + 1) → ℝ)
    (child : Fin 3) (corner : TriangleCorner) :
    x (sgChildVertex m child (sgLevelOuterCorner m corner)) =
      sgParentBoundaryRestriction m x
        (sgChildCornerBoundaryIndex child corner) := by
  rw [sgChildCorner_maps_parentBoundary]
  rfl


/-- The interior vertices of one child, after removing the retained
six-point boundary of the parent. -/
noncomputable def sgChildInteriorSet (m : Nat) (child : Fin 3) :
    Finset (SGVertex (m + 1)) :=
  sgChildVertexSet m child \ sgParentBoundarySet m

theorem sgParentMidpoint01_mem_boundary (m : Nat) :
    sgParentMidpoint01 m ∈ sgParentBoundarySet m := by
  change sgParentMidpoint01 m ∈
    Finset.univ.image (sgParentBoundaryVertex m)
  exact Finset.mem_image.mpr
    ⟨(3 : Fin 6), Finset.mem_univ _, by simp [sgParentBoundaryVertex]⟩

theorem sgParentMidpoint02_mem_boundary (m : Nat) :
    sgParentMidpoint02 m ∈ sgParentBoundarySet m := by
  change sgParentMidpoint02 m ∈
    Finset.univ.image (sgParentBoundaryVertex m)
  exact Finset.mem_image.mpr
    ⟨(4 : Fin 6), Finset.mem_univ _, by simp [sgParentBoundaryVertex]⟩

theorem sgParentMidpoint12_mem_boundary (m : Nat) :
    sgParentMidpoint12 m ∈ sgParentBoundarySet m := by
  change sgParentMidpoint12 m ∈
    Finset.univ.image (sgParentBoundaryVertex m)
  exact Finset.mem_image.mpr
    ⟨(5 : Fin 6), Finset.mem_univ _, by simp [sgParentBoundaryVertex]⟩

theorem sgChildInteriorSet_disjoint_zero_one (m : Nat) :
    Disjoint (sgChildInteriorSet m 0) (sgChildInteriorSet m 1) := by
  rw [Finset.disjoint_left]
  intro v hv0 hv1
  have hv0' := (Finset.mem_sdiff.mp hv0).1
  have hv1' := (Finset.mem_sdiff.mp hv1).1
  have hnot := (Finset.mem_sdiff.mp hv0).2
  have hinter :
      v ∈ sgChildVertexSet m 0 ∩ sgChildVertexSet m 1 :=
    Finset.mem_inter.mpr ⟨hv0', hv1'⟩
  rw [sgChildVertexSet_inter_zero_one] at hinter
  have hmid : v = sgParentMidpoint01 m :=
    Finset.mem_singleton.mp hinter
  exact hnot (hmid.symm ▸ sgParentMidpoint01_mem_boundary m)

theorem sgChildInteriorSet_disjoint_zero_two (m : Nat) :
    Disjoint (sgChildInteriorSet m 0) (sgChildInteriorSet m 2) := by
  rw [Finset.disjoint_left]
  intro v hv0 hv2
  have hv0' := (Finset.mem_sdiff.mp hv0).1
  have hv2' := (Finset.mem_sdiff.mp hv2).1
  have hnot := (Finset.mem_sdiff.mp hv0).2
  have hinter :
      v ∈ sgChildVertexSet m 0 ∩ sgChildVertexSet m 2 :=
    Finset.mem_inter.mpr ⟨hv0', hv2'⟩
  rw [sgChildVertexSet_inter_zero_two] at hinter
  have hmid : v = sgParentMidpoint02 m :=
    Finset.mem_singleton.mp hinter
  exact hnot (hmid.symm ▸ sgParentMidpoint02_mem_boundary m)

theorem sgChildInteriorSet_disjoint_one_two (m : Nat) :
    Disjoint (sgChildInteriorSet m 1) (sgChildInteriorSet m 2) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  have hv1' := (Finset.mem_sdiff.mp hv1).1
  have hv2' := (Finset.mem_sdiff.mp hv2).1
  have hnot := (Finset.mem_sdiff.mp hv1).2
  have hinter :
      v ∈ sgChildVertexSet m 1 ∩ sgChildVertexSet m 2 :=
    Finset.mem_inter.mpr ⟨hv1', hv2'⟩
  rw [sgChildVertexSet_inter_one_two] at hinter
  have hmid : v = sgParentMidpoint12 m :=
    Finset.mem_singleton.mp hinter
  exact hnot (hmid.symm ▸ sgParentMidpoint12_mem_boundary m)

/-- The parent interior is exactly the union of the three child interiors.
The child interiors are pairwise disjoint by the preceding lemmas. -/
theorem sgChildInteriorSet_union (m : Nat) :
    sgChildInteriorSet m 0 ∪
      sgChildInteriorSet m 1 ∪
      sgChildInteriorSet m 2 =
    sgParentInteriorSet m := by
  classical
  ext v
  simp only [sgChildInteriorSet, sgParentInteriorSet,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ]
  constructor
  · rintro ((⟨_, hnot⟩ | ⟨_, hnot⟩) | ⟨_, hnot⟩)
    all_goals exact ⟨True.intro, hnot⟩
  · rintro ⟨_, hnot⟩
    have hcover :
        v ∈ sgChildVertexSet m 0 ∪
          sgChildVertexSet m 1 ∪
          sgChildVertexSet m 2 := by
      rw [sgChildVertexSet_union]
      simp
    rcases Finset.mem_union.mp hcover with h01 | h2
    · rcases Finset.mem_union.mp h01 with h0 | h1
      · exact Or.inl (Or.inl ⟨h0, hnot⟩)
      · exact Or.inl (Or.inr ⟨h1, hnot⟩)
    · exact Or.inr ⟨h2, hnot⟩


/-- An interior vertex of one child cannot belong to a different
child copy: their only intersection is part of the retained boundary. -/
theorem sgChildInteriorSet_not_mem_other_child
    (m : Nat) {i j : Fin 3} (hij : i ≠ j)
    {v : SGVertex (m + 1)}
    (hv : v ∈ sgChildInteriorSet m i) :
    v ∉ sgChildVertexSet m j := by
  classical
  intro hvj
  have hnotBoundary : v ∉ sgParentBoundarySet m :=
    (Finset.mem_sdiff.mp hv).2
  have hChild : v ∈ sgChildVertexSet m i :=
    (Finset.mem_sdiff.mp hv).1
  have hboundary : v ∈ sgParentBoundarySet m := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    ·
      have hmem :
          v ∈ sgChildVertexSet m 0 ∩ sgChildVertexSet m 1 :=
        Finset.mem_inter.mpr ⟨hChild, hvj⟩
      rw [sgChildVertexSet_inter_zero_one] at hmem
      have heq : v = sgParentMidpoint01 m :=
        Finset.mem_singleton.mp hmem
      exact heq.symm ▸ sgParentMidpoint01_mem_boundary m
    ·
      have hmem :
          v ∈ sgChildVertexSet m 0 ∩ sgChildVertexSet m 2 :=
        Finset.mem_inter.mpr ⟨hChild, hvj⟩
      rw [sgChildVertexSet_inter_zero_two] at hmem
      have heq : v = sgParentMidpoint02 m :=
        Finset.mem_singleton.mp hmem
      exact heq.symm ▸ sgParentMidpoint02_mem_boundary m
    ·
      have hmem :
          v ∈ sgChildVertexSet m 0 ∩ sgChildVertexSet m 1 :=
        Finset.mem_inter.mpr ⟨hvj, hChild⟩
      rw [sgChildVertexSet_inter_zero_one] at hmem
      have heq : v = sgParentMidpoint01 m :=
        Finset.mem_singleton.mp hmem
      exact heq.symm ▸ sgParentMidpoint01_mem_boundary m
    · exact False.elim (hij rfl)
    ·
      have hmem :
          v ∈ sgChildVertexSet m 1 ∩ sgChildVertexSet m 2 :=
        Finset.mem_inter.mpr ⟨hChild, hvj⟩
      rw [sgChildVertexSet_inter_one_two] at hmem
      have heq : v = sgParentMidpoint12 m :=
        Finset.mem_singleton.mp hmem
      exact heq.symm ▸ sgParentMidpoint12_mem_boundary m
    ·
      have hmem :
          v ∈ sgChildVertexSet m 0 ∩ sgChildVertexSet m 2 :=
        Finset.mem_inter.mpr ⟨hvj, hChild⟩
      rw [sgChildVertexSet_inter_zero_two] at hmem
      have heq : v = sgParentMidpoint02 m :=
        Finset.mem_singleton.mp hmem
      exact heq.symm ▸ sgParentMidpoint02_mem_boundary m
    ·
      have hmem :
          v ∈ sgChildVertexSet m 1 ∩ sgChildVertexSet m 2 :=
        Finset.mem_inter.mpr ⟨hvj, hChild⟩
      rw [sgChildVertexSet_inter_one_two] at hmem
      have heq : v = sgParentMidpoint12 m :=
        Finset.mem_singleton.mp hmem
      exact heq.symm ▸ sgParentMidpoint12_mem_boundary m
    · exact False.elim (hij rfl)
  exact hnotBoundary hboundary

theorem sgEdgeIndicator_childEdge_eq_zero_of_not_mem
    (m : Nat) (child : Fin 3)
    (a b : SGVertex m) (v : SGVertex (m + 1))
    (hv : v ∉ sgChildVertexSet m child) :
    sgEdgeIndicator (m + 1)
      (sgChildVertex m child a, sgChildVertex m child b) v = 0 := by
  have ha : v ≠ sgChildVertex m child a := by
    intro h
    apply hv
    change v ∈ Finset.univ.image (sgChildVertex m child)
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_univ a, h.symm⟩
  have hb : v ≠ sgChildVertex m child b := by
    intro h
    apply hv
    change v ∈ Finset.univ.image (sgChildVertex m child)
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_univ b, h.symm⟩
  simp [sgEdgeIndicator, ha, hb]

/-- The shifted decomposition has no matrix coupling between
interior vertices belonging to different child copies. -/
theorem sgSignlessLaplacianMatrix_childInterior_mixed_eq_zero
    (m : Nat) {i j : Fin 3} (hij : i ≠ j)
    {u v : SGVertex (m + 1)}
    (hu : u ∈ sgChildInteriorSet m i)
    (hv : v ∈ sgChildInteriorSet m j) :
    sgSignlessLaplacianMatrix (m + 1) u v = 0 := by
  classical
  rw [sgSignlessLaplacianMatrix_eq_childSlotSum]
  apply Finset.sum_eq_zero
  intro q hq
  rcases q with ⟨k, e⟩
  by_cases hki : k = i
  · subst k
    have hvnot : v ∉ sgChildVertexSet m i :=
      sgChildInteriorSet_not_mem_other_child m hij.symm hv
    have hz :
        sgEdgeIndicator (m + 1)
          (sgChildVertex m i
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
              (sgFaceC m) e).1,
           sgChildVertex m i
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
              (sgFaceC m) e).2) v = 0 :=
      sgEdgeIndicator_childEdge_eq_zero_of_not_mem
        m i
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) e).1
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) e).2
        v hvnot
    simp [hz]
  · have hunot : u ∉ sgChildVertexSet m k :=
      sgChildInteriorSet_not_mem_other_child m
        (Ne.symm hki) hu
    have hz :
        sgEdgeIndicator (m + 1)
          (sgChildVertex m k
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
              (sgFaceC m) e).1,
           sgChildVertex m k
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
              (sgFaceC m) e).2) u = 0 :=
      sgEdgeIndicator_childEdge_eq_zero_of_not_mem
        m k
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) e).1
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) e).2
        u hunot
    simp [hz]


/-- Edge incidence is preserved by the injective embedding of a child. -/
theorem sgEdgeIndicator_child_map
    (m : Nat) (child : Fin 3)
    (a b c : SGVertex m) :
    sgEdgeIndicator (m + 1)
      (sgChildVertex m child a, sgChildVertex m child b)
      (sgChildVertex m child c) =
    sgEdgeIndicator m (a, b) c := by
  have hca :
      (sgChildVertex m child c = sgChildVertex m child a) ↔ c = a := by
    constructor
    · intro h
      exact sgChildVertex_injective m child h
    · intro h
      cases h
      rfl
  have hcb :
      (sgChildVertex m child c = sgChildVertex m child b) ↔ c = b := by
    constructor
    · intro h
      exact sgChildVertex_injective m child h
    · intro h
      cases h
      rfl
  simp [sgEdgeIndicator, hca, hcb]

/-- A matrix entry with its first vertex in a child interior is exactly
the corresponding entry of that child's signless Laplacian. -/
theorem sgSignlessLaplacianMatrix_childInterior_entry
    (m : Nat) (i : Fin 3)
    (a b : SGVertex m)
    (ha : sgChildVertex m i a ∈ sgChildInteriorSet m i) :
    sgSignlessLaplacianMatrix (m + 1)
        (sgChildVertex m i a) (sgChildVertex m i b) =
      sgSignlessLaplacianMatrix m a b := by
  classical
  let edgeTerm (k : Fin 3)
      (p : (Fin m → Fin 3) × TriangleEdge) : ℝ :=
    sgEdgeIndicator (m + 1)
      (sgChildVertex m k
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).1,
       sgChildVertex m k
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).2)
      (sgChildVertex m i a) *
    sgEdgeIndicator (m + 1)
      (sgChildVertex m k
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).1,
       sgChildVertex m k
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).2)
      (sgChildVertex m i b)

  have hzero (k : Fin 3) (hki : k ≠ i) :
      (∑ p : (Fin m → Fin 3) × TriangleEdge, edgeTerm k p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have huNot :
        sgChildVertex m i a ∉ sgChildVertexSet m k :=
      sgChildInteriorSet_not_mem_other_child m (Ne.symm hki) ha
    have hinc :
        sgEdgeIndicator (m + 1)
          (sgChildVertex m k
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
              (sgFaceC m) p).1,
           sgChildVertex m k
            (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
              (sgFaceC m) p).2)
          (sgChildVertex m i a) = 0 :=
      sgEdgeIndicator_childEdge_eq_zero_of_not_mem
        m k
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).1
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m)
          (sgFaceC m) p).2
        (sgChildVertex m i a) huNot
    simp [edgeTerm, hinc]

  have hmain :
      (∑ p : (Fin m → Fin 3) × TriangleEdge, edgeTerm i p) =
        sgSignlessLaplacianMatrix m a b := by
    rw [sgSignlessLaplacianMatrix_eq_slotSum]
    apply Finset.sum_congr rfl
    intro p hp
    simp [edgeTerm, sgEdgeIndicator_child_map]

  have hsum3 (g : Fin 3 → ℝ) :
      (∑ k : Fin 3, g k) = g 0 + g 1 + g 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h1 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
    have h2 : Fin.succ (Fin.succ (0 : Fin 1)) = (2 : Fin 3) := by decide
    rw [h1, h2, Fin.sum_univ_zero]
    ring

  rw [sgSignlessLaplacianMatrix_eq_childSlotSum,
    Fintype.sum_prod_type]
  change
    (∑ k : Fin 3,
      ∑ p : (Fin m → Fin 3) × TriangleEdge, edgeTerm k p) =
      sgSignlessLaplacianMatrix m a b
  rw [hsum3]
  fin_cases i
  · rw [hzero 1 (by decide), hzero 2 (by decide)]
    simpa using hmain
  · rw [hzero 0 (by decide), hzero 2 (by decide)]
    simpa using hmain
  · rw [hzero 0 (by decide), hzero 1 (by decide)]
    simpa using hmain


/-- The shifted parent matrix restricts on one child interior
to the correspondingly shifted child matrix. -/
theorem sgSignlessShiftedMatrix_childInterior_entry
    (m : Nat) (lambda : ℝ) (i : Fin 3)
    (a b : SGVertex m)
    (ha : sgChildVertex m i a ∈ sgChildInteriorSet m i) :
    (sgSignlessLaplacianMatrix (m + 1) -
      lambda • (1 : Matrix (SGVertex (m + 1))
        (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) (sgChildVertex m i b) =
    (sgSignlessLaplacianMatrix m -
      lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) a b := by
  have hEq :
      (sgChildVertex m i a = sgChildVertex m i b) ↔ a = b := by
    constructor
    · intro h
      exact sgChildVertex_injective m i h
    · intro h
      cases h
      rfl
  simp [Matrix.sub_apply, Matrix.one_apply,
    sgSignlessLaplacianMatrix_childInterior_entry m i a b ha, hEq]


/-- The shifted parent matrix, restricted to child interiors, is
block diagonal: diagonal blocks are the shifted child matrices and
all cross-child blocks vanish. -/
theorem sgSignlessShiftedMatrix_childInterior_blockEntry
    (m : Nat) (lambda : ℝ)
    (i j : Fin 3) (a b : SGVertex m)
    (ha : sgChildVertex m i a ∈ sgChildInteriorSet m i)
    (hb : sgChildVertex m j b ∈ sgChildInteriorSet m j) :
    (sgSignlessLaplacianMatrix (m + 1) -
      lambda • (1 : Matrix (SGVertex (m + 1))
        (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) (sgChildVertex m j b) =
    if i = j then
      (sgSignlessLaplacianMatrix m -
        lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) a b
    else 0 := by
  by_cases hij : i = j
  · subst j
    simp [sgSignlessShiftedMatrix_childInterior_entry
      m lambda i a b ha]
  · have huv : sgChildVertex m i a ≠ sgChildVertex m j b := by
      intro heq
      have hvmem :
          sgChildVertex m j b ∈ sgChildVertexSet m j :=
        (Finset.mem_sdiff.mp hb).1
      have huout :
          sgChildVertex m i a ∉ sgChildVertexSet m j :=
        sgChildInteriorSet_not_mem_other_child m hij ha
      have humem :
          sgChildVertex m i a ∈ sgChildVertexSet m j := by
        rw [heq]
        exact hvmem
      exact huout humem
    have hzero :
        sgSignlessLaplacianMatrix (m + 1)
          (sgChildVertex m i a) (sgChildVertex m j b) = 0 :=
      sgSignlessLaplacianMatrix_childInterior_mixed_eq_zero
        m hij ha hb
    simp [Matrix.sub_apply, Matrix.one_apply, hzero, huv, hij]


/-- A parent-interior vertex belonging to one child has no shifted
matrix coupling to vertices outside that child's copy. -/
theorem sgSignlessShiftedMatrix_childInterior_outsideChild_eq_zero
    (m : Nat) (lambda : ℝ) (i : Fin 3)
    (a : SGVertex m) (ha :
      sgChildVertex m i a ∈ sgChildInteriorSet m i)
    (v : SGVertex (m + 1))
    (hv : v ∉ sgChildVertexSet m i) :
    (sgSignlessLaplacianMatrix (m + 1) -
      lambda • (1 : Matrix (SGVertex (m + 1))
        (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) v = 0 := by
  classical
  have hu : sgChildVertex m i a ∈ sgChildVertexSet m i :=
    (Finset.mem_sdiff.mp ha).1
  have huv : sgChildVertex m i a ≠ v := by
    intro h
    apply hv
    rw [← h]
    exact hu

  have hQ :
      sgSignlessLaplacianMatrix (m + 1)
        (sgChildVertex m i a) v = 0 := by
    rw [sgSignlessLaplacianMatrix_eq_childSlotSum]
    apply Finset.sum_eq_zero
    intro q hq
    rcases q with ⟨k, e⟩
    let endpoints :=
      faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) e
    by_cases hki : k = i
    · subst k
      have hvzero :
          sgEdgeIndicator (m + 1)
            (sgChildVertex m i endpoints.1,
             sgChildVertex m i endpoints.2) v = 0 :=
        sgEdgeIndicator_childEdge_eq_zero_of_not_mem
          m i endpoints.1 endpoints.2 v hv
      exact mul_eq_zero.mpr
        (Or.inr (by simpa [endpoints] using hvzero))
    · have hunot : sgChildVertex m i a ∉ sgChildVertexSet m k :=
        sgChildInteriorSet_not_mem_other_child m (Ne.symm hki) ha
      have huzero :
          sgEdgeIndicator (m + 1)
            (sgChildVertex m k endpoints.1,
             sgChildVertex m k endpoints.2)
            (sgChildVertex m i a) = 0 :=
        sgEdgeIndicator_childEdge_eq_zero_of_not_mem
          m k endpoints.1 endpoints.2
          (sgChildVertex m i a) hunot
      exact mul_eq_zero.mpr
        (Or.inl (by simpa [endpoints] using huzero))

  simp [Matrix.sub_apply, Matrix.one_apply, hQ, huv]


/-- For a vertex interior to one child copy, its complete parent
shifted-matrix row is the corresponding child row, extended by zero
outside that copy. This is the row identity used to compose the
three child Dirichlet reductions. -/
theorem sgSignlessShiftedMatrix_childInterior_row_eq_childRow
    (m : Nat) (lambda : ℝ) (i : Fin 3)
    (a : SGVertex m)
    (ha : sgChildVertex m i a ∈ sgChildInteriorSet m i)
    (x : SGVertex (m + 1) → ℝ) :
    (∑ v : SGVertex (m + 1),
      (sgSignlessLaplacianMatrix (m + 1) -
        lambda • (1 : Matrix (SGVertex (m + 1))
          (SGVertex (m + 1)) ℝ))
        (sgChildVertex m i a) v * x v) =
    (∑ b : SGVertex m,
      (sgSignlessLaplacianMatrix m -
        lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ))
        a b * x (sgChildVertex m i b)) := by
  classical
  let A : Finset (SGVertex (m + 1)) :=
    sgChildVertexSet m i
  let f : SGVertex (m + 1) → ℝ := fun v =>
    (sgSignlessLaplacianMatrix (m + 1) -
      lambda • (1 : Matrix (SGVertex (m + 1))
        (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) v * x v

  have hdisj :
      Disjoint A
        ((Finset.univ : Finset (SGVertex (m + 1))) \ A) := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvComp
    exact (Finset.mem_sdiff.mp hvComp).2 hvA

  have hcover :
      A ∪
        ((Finset.univ : Finset (SGVertex (m + 1))) \ A) =
      Finset.univ := by
    ext v
    simp [A]

  have hOutside :
      (∑ v ∈
        (Finset.univ : Finset (SGVertex (m + 1))) \ A, f v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hvnot : v ∉ sgChildVertexSet m i := by
      simpa [A] using (Finset.mem_sdiff.mp hv).2
    change
      ((sgSignlessLaplacianMatrix (m + 1) -
        lambda • (1 : Matrix (SGVertex (m + 1))
          (SGVertex (m + 1)) ℝ))
        (sgChildVertex m i a) v) * x v = 0
    rw [sgSignlessShiftedMatrix_childInterior_outsideChild_eq_zero
      m lambda i a ha v hvnot]
    simp

  have hi : Set.InjOn (sgChildVertex m i)
      (↑(Finset.univ : Finset (SGVertex m))) := by
    intro u hu v hv huv
    exact sgChildVertex_injective m i huv

  have hImage :
      (∑ b : SGVertex m, f (sgChildVertex m i b)) =
        (∑ v ∈ A, f v) := by
    dsimp [A, sgChildVertexSet]
    rw [Finset.sum_image hi]

  have hInside :
      (∑ v ∈ A, f v) =
        (∑ b : SGVertex m,
          (sgSignlessLaplacianMatrix m -
            lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ))
            a b * x (sgChildVertex m i b)) := by
    rw [← hImage]
    apply Finset.sum_congr rfl
    intro b hb
    change
      ((sgSignlessLaplacianMatrix (m + 1) -
        lambda • (1 : Matrix (SGVertex (m + 1))
          (SGVertex (m + 1)) ℝ))
        (sgChildVertex m i a) (sgChildVertex m i b)) *
          x (sgChildVertex m i b) =
      ((sgSignlessLaplacianMatrix m -
        lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ))
        a b) * x (sgChildVertex m i b)
    rw [sgSignlessShiftedMatrix_childInterior_entry
      m lambda i a b ha]

  have hTotal :
      (∑ v : SGVertex (m + 1), f v) =
        (∑ v ∈ A, f v) +
          (∑ v ∈
            (Finset.univ : Finset (SGVertex (m + 1))) \ A, f v) := by
    calc
      _ = (∑ v ∈ A ∪
          ((Finset.univ : Finset (SGVertex (m + 1))) \ A), f v) := by
            rw [hcover]
      _ = _ := Finset.sum_union hdisj

  calc
    _ = (∑ v ∈ A, f v) +
          (∑ v ∈
            (Finset.univ : Finset (SGVertex (m + 1))) \ A, f v) :=
      hTotal
    _ = ∑ v ∈ A, f v := by rw [hOutside]; simp
    _ = _ := hInside



/-- The parent interior stationarity equations are equivalent to
the three independent child interior stationarity systems. This is
the operator-level decomposition needed for the inductive Schur
reduction. -/
theorem sgSignlessShiftedMatrix_parentInterior_rows_iff_childInterior_rows
    (m : Nat) (lambda : ℝ) (x : SGVertex (m + 1) → ℝ) :
    (∀ v : SGVertex (m + 1),
      v ∈ sgParentInteriorSet m →
      (∑ w : SGVertex (m + 1),
        (sgSignlessLaplacianMatrix (m + 1) -
          lambda • (1 : Matrix (SGVertex (m + 1))
            (SGVertex (m + 1)) ℝ)) v w * x w) = 0) ↔
    (∀ i : Fin 3, ∀ a : SGVertex m,
      sgChildVertex m i a ∈ sgChildInteriorSet m i →
      (∑ b : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ))
          a b * x (sgChildVertex m i b)) = 0) := by
  classical
  constructor
  · intro h i a ha
    have hparent :
        sgChildVertex m i a ∈ sgParentInteriorSet m := by
      rw [← sgChildInteriorSet_union m]
      fin_cases i <;> simp_all
    have hrow :=
      sgSignlessShiftedMatrix_childInterior_row_eq_childRow
        m lambda i a ha x
    have hz := h (sgChildVertex m i a) hparent
    rw [hrow] at hz
    exact hz

  · intro h
    have hrowAt (i : Fin 3) (a : SGVertex m)
        (ha : sgChildVertex m i a ∈ sgChildInteriorSet m i) :
        (∑ w : SGVertex (m + 1),
          (sgSignlessLaplacianMatrix (m + 1) -
            lambda • (1 : Matrix (SGVertex (m + 1))
              (SGVertex (m + 1)) ℝ))
            (sgChildVertex m i a) w * x w) = 0 := by
      calc
        _ =
          (∑ b : SGVertex m,
            (sgSignlessLaplacianMatrix m -
              lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ))
              a b * x (sgChildVertex m i b)) :=
          sgSignlessShiftedMatrix_childInterior_row_eq_childRow
            m lambda i a ha x
        _ = 0 := h i a ha

    intro v hv
    rw [← sgChildInteriorSet_union m] at hv
    rcases Finset.mem_union.mp hv with hv01 | hv2
    · rcases Finset.mem_union.mp hv01 with hv0 | hv1
      · have hvA : v ∈ sgChildVertexSet m 0 :=
          (Finset.mem_sdiff.mp
            (show v ∈ sgChildVertexSet m 0 \ sgParentBoundarySet m from
              by simpa [sgChildInteriorSet] using hv0)).1
        have hImage :
            v ∈ (Finset.univ : Finset (SGVertex m)).image
              (sgChildVertex m 0) := by
          simpa [sgChildVertexSet] using hvA
        rcases Finset.mem_image.mp hImage with ⟨a, -, hav⟩
        have ha : sgChildVertex m 0 a ∈ sgChildInteriorSet m 0 := by
          simpa [hav] using hv0
        calc
          _ =
            (∑ w : SGVertex (m + 1),
              (sgSignlessLaplacianMatrix (m + 1) -
                lambda • (1 : Matrix (SGVertex (m + 1))
                  (SGVertex (m + 1)) ℝ))
                (sgChildVertex m 0 a) w * x w) := by
                  rw [← hav]
          _ = 0 := hrowAt 0 a ha

      · have hvB : v ∈ sgChildVertexSet m 1 :=
          (Finset.mem_sdiff.mp
            (show v ∈ sgChildVertexSet m 1 \ sgParentBoundarySet m from
              by simpa [sgChildInteriorSet] using hv1)).1
        have hImage :
            v ∈ (Finset.univ : Finset (SGVertex m)).image
              (sgChildVertex m 1) := by
          simpa [sgChildVertexSet] using hvB
        rcases Finset.mem_image.mp hImage with ⟨a, -, hav⟩
        have ha : sgChildVertex m 1 a ∈ sgChildInteriorSet m 1 := by
          simpa [hav] using hv1
        calc
          _ =
            (∑ w : SGVertex (m + 1),
              (sgSignlessLaplacianMatrix (m + 1) -
                lambda • (1 : Matrix (SGVertex (m + 1))
                  (SGVertex (m + 1)) ℝ))
                (sgChildVertex m 1 a) w * x w) := by
                  rw [← hav]
          _ = 0 := hrowAt 1 a ha

    · have hvC : v ∈ sgChildVertexSet m 2 :=
        (Finset.mem_sdiff.mp
          (show v ∈ sgChildVertexSet m 2 \ sgParentBoundarySet m from
            by simpa [sgChildInteriorSet] using hv2)).1
      have hImage :
          v ∈ (Finset.univ : Finset (SGVertex m)).image
            (sgChildVertex m 2) := by
        simpa [sgChildVertexSet] using hvC
      rcases Finset.mem_image.mp hImage with ⟨a, -, hav⟩
      have ha : sgChildVertex m 2 a ∈ sgChildInteriorSet m 2 := by
        simpa [hav] using hv2
      calc
        _ =
          (∑ w : SGVertex (m + 1),
            (sgSignlessLaplacianMatrix (m + 1) -
              lambda • (1 : Matrix (SGVertex (m + 1))
                (SGVertex (m + 1)) ℝ))
              (sgChildVertex m 2 a) w * x w) := by
                rw [← hav]
        _ = 0 := hrowAt 2 a ha



/-- The bilinear form associated with the shifted signless
Laplacian matrix. -/
noncomputable def sgSignlessShiftedBilinearForm
    (m : Nat) (lambda : ℝ)
    (x y : SGVertex m → ℝ) : ℝ :=
  ∑ u : SGVertex m, x u *
    ∑ v : SGVertex m,
      (sgSignlessLaplacianMatrix m -
        lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * y v

/-- The shifted signless matrix, and hence its bilinear form,
is symmetric. -/
theorem sgSignlessShiftedBilinearForm_symm
    (m : Nat) (lambda : ℝ)
    (x y : SGVertex m → ℝ) :
    sgSignlessShiftedBilinearForm m lambda x y =
      sgSignlessShiftedBilinearForm m lambda y x := by
  classical
  have hS (u v : SGVertex m) :
      (sgSignlessLaplacianMatrix m -
        lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v =
      (sgSignlessLaplacianMatrix m -
        lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) v u := by
    simp [Matrix.sub_apply, Matrix.one_apply,
      sgSignlessLaplacianMatrix, mul_comm]
    by_cases h : u = v
    · subst h; rfl
    · simp [h, Ne.symm h]
  calc
    _ = ∑ u : SGVertex m, ∑ v : SGVertex m,
        x u *
          ((sgSignlessLaplacianMatrix m -
            lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
            y v) := by
          simp only [sgSignlessShiftedBilinearForm, Finset.mul_sum]
    _ = ∑ v : SGVertex m, ∑ u : SGVertex m,
        x u *
          ((sgSignlessLaplacianMatrix m -
            lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
            y v) := by
          exact Finset.sum_comm
    _ = ∑ v : SGVertex m, y v *
        ∑ u : SGVertex m,
          (sgSignlessLaplacianMatrix m -
            lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) v u *
            x u := by
          apply Finset.sum_congr rfl
          intro v hv
          calc
            _ = ∑ u : SGVertex m, y v *
                ((sgSignlessLaplacianMatrix m -
                  lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) v u *
                  x u) := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  rw [hS]
                  ring
            _ = _ := by rw [← Finset.mul_sum]
    _ = _ := rfl

/-- Polarization: the symmetric bilinear form is recovered from
the quadratic form by expanding `x + y`. -/
theorem sgSignlessShiftedBilinearForm_polarization
    (m : Nat) (lambda : ℝ)
    (x y : SGVertex m → ℝ) :
    sgSignlessShiftedBilinearForm m lambda
        (fun v => x v + y v) (fun v => x v + y v) =
      sgSignlessShiftedBilinearForm m lambda x x +
      sgSignlessShiftedBilinearForm m lambda y y +
      2 * sgSignlessShiftedBilinearForm m lambda x y := by
  classical
  have hinner (u : SGVertex m) :
      (∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          (x v + y v)) =
      (∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          x v) +
      (∑ v : SGVertex m,
        (sgSignlessLaplacianMatrix m -
          lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
          y v) := by
    calc
      _ = ∑ v : SGVertex m,
          ((sgSignlessLaplacianMatrix m -
            lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              x v +
           (sgSignlessLaplacianMatrix m -
            lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              y v) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = _ := Finset.sum_add_distrib
  calc
    _ = ∑ u : SGVertex m,
        (x u + y u) *
          ((∑ v : SGVertex m,
            (sgSignlessLaplacianMatrix m -
              lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              x v) +
           (∑ v : SGVertex m,
            (sgSignlessLaplacianMatrix m -
              lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              y v)) := by
          unfold sgSignlessShiftedBilinearForm
          apply Finset.sum_congr rfl
          intro u hu
          rw [hinner u]
    _ = ∑ u : SGVertex m,
        (x u *
          (∑ v : SGVertex m,
            (sgSignlessLaplacianMatrix m -
              lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              x v) +
         x u *
          (∑ v : SGVertex m,
            (sgSignlessLaplacianMatrix m -
              lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              y v) +
         y u *
          (∑ v : SGVertex m,
            (sgSignlessLaplacianMatrix m -
              lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              x v) +
         y u *
          (∑ v : SGVertex m,
            (sgSignlessLaplacianMatrix m -
              lambda • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v *
              y v)) := by
          apply Finset.sum_congr rfl
          intro u hu
          ring
    _ = sgSignlessShiftedBilinearForm m lambda x x +
        sgSignlessShiftedBilinearForm m lambda x y +
        sgSignlessShiftedBilinearForm m lambda y x +
        sgSignlessShiftedBilinearForm m lambda y y := by
          simp only [sgSignlessShiftedBilinearForm,
            Finset.sum_add_distrib]
    _ = _ := by
          rw [sgSignlessShiftedBilinearForm_symm m lambda y x]
          ring

/-- Exact bilinear decomposition of the parent shifted matrix into
the three child shifted matrices. The three shared midpoints contribute
the correction `lambda * x(midpoint) * y(midpoint)`. -/
theorem sgSignlessShiftedBilinearForm_childDecomposition
    (m : Nat) (lambda : ℝ)
    (x y : SGVertex (m + 1) → ℝ) :
    sgSignlessShiftedBilinearForm (m + 1) lambda x y =
      sgSignlessShiftedBilinearForm m lambda
        (fun v => x (sgChildVertex m 0 v))
        (fun v => y (sgChildVertex m 0 v)) +
      sgSignlessShiftedBilinearForm m lambda
        (fun v => x (sgChildVertex m 1 v))
        (fun v => y (sgChildVertex m 1 v)) +
      sgSignlessShiftedBilinearForm m lambda
        (fun v => x (sgChildVertex m 2 v))
        (fun v => y (sgChildVertex m 2 v)) +
      lambda *
        (x (sgParentMidpoint01 m) * y (sgParentMidpoint01 m) +
         x (sgParentMidpoint02 m) * y (sgParentMidpoint02 m) +
         x (sgParentMidpoint12 m) * y (sgParentMidpoint12 m)) := by
  classical
  have hParentPol :=
    sgSignlessShiftedBilinearForm_polarization
      (m + 1) lambda x y
  have hChild0Pol :=
    sgSignlessShiftedBilinearForm_polarization m lambda
      (fun v => x (sgChildVertex m 0 v))
      (fun v => y (sgChildVertex m 0 v))
  have hChild1Pol :=
    sgSignlessShiftedBilinearForm_polarization m lambda
      (fun v => x (sgChildVertex m 1 v))
      (fun v => y (sgChildVertex m 1 v))
  have hChild2Pol :=
    sgSignlessShiftedBilinearForm_polarization m lambda
      (fun v => x (sgChildVertex m 2 v))
      (fun v => y (sgChildVertex m 2 v))

  have hDecompSum :
      sgSignlessShiftedBilinearForm (m + 1) lambda
          (fun v => x v + y v) (fun v => x v + y v) =
        sgSignlessShiftedBilinearForm m lambda
          (fun v => x (sgChildVertex m 0 v) +
            y (sgChildVertex m 0 v))
          (fun v => x (sgChildVertex m 0 v) +
            y (sgChildVertex m 0 v)) +
        sgSignlessShiftedBilinearForm m lambda
          (fun v => x (sgChildVertex m 1 v) +
            y (sgChildVertex m 1 v))
          (fun v => x (sgChildVertex m 1 v) +
            y (sgChildVertex m 1 v)) +
        sgSignlessShiftedBilinearForm m lambda
          (fun v => x (sgChildVertex m 2 v) +
            y (sgChildVertex m 2 v))
          (fun v => x (sgChildVertex m 2 v) +
            y (sgChildVertex m 2 v)) +
        lambda *
          ((x (sgParentMidpoint01 m) + y (sgParentMidpoint01 m)) ^ 2 +
           (x (sgParentMidpoint02 m) + y (sgParentMidpoint02 m)) ^ 2 +
           (x (sgParentMidpoint12 m) + y (sgParentMidpoint12 m)) ^ 2) := by
    simpa only [sgSignlessShiftedBilinearForm] using
      sgSignlessShiftedMatrix_childDecomposition
        m lambda (fun v => x v + y v)

  have hDecompX :
      sgSignlessShiftedBilinearForm (m + 1) lambda x x =
        sgSignlessShiftedBilinearForm m lambda
          (fun v => x (sgChildVertex m 0 v))
          (fun v => x (sgChildVertex m 0 v)) +
        sgSignlessShiftedBilinearForm m lambda
          (fun v => x (sgChildVertex m 1 v))
          (fun v => x (sgChildVertex m 1 v)) +
        sgSignlessShiftedBilinearForm m lambda
          (fun v => x (sgChildVertex m 2 v))
          (fun v => x (sgChildVertex m 2 v)) +
        lambda *
          (x (sgParentMidpoint01 m) ^ 2 +
           x (sgParentMidpoint02 m) ^ 2 +
           x (sgParentMidpoint12 m) ^ 2) := by
    simpa only [sgSignlessShiftedBilinearForm] using
      sgSignlessShiftedMatrix_childDecomposition m lambda x

  have hDecompY :
      sgSignlessShiftedBilinearForm (m + 1) lambda y y =
        sgSignlessShiftedBilinearForm m lambda
          (fun v => y (sgChildVertex m 0 v))
          (fun v => y (sgChildVertex m 0 v)) +
        sgSignlessShiftedBilinearForm m lambda
          (fun v => y (sgChildVertex m 1 v))
          (fun v => y (sgChildVertex m 1 v)) +
        sgSignlessShiftedBilinearForm m lambda
          (fun v => y (sgChildVertex m 2 v))
          (fun v => y (sgChildVertex m 2 v)) +
        lambda *
          (y (sgParentMidpoint01 m) ^ 2 +
           y (sgParentMidpoint02 m) ^ 2 +
           y (sgParentMidpoint12 m) ^ 2) := by
    simpa only [sgSignlessShiftedBilinearForm] using
      sgSignlessShiftedMatrix_childDecomposition m lambda y

  have htwice :
      2 * sgSignlessShiftedBilinearForm (m + 1) lambda x y =
        2 *
          (sgSignlessShiftedBilinearForm m lambda
            (fun v => x (sgChildVertex m 0 v))
            (fun v => y (sgChildVertex m 0 v)) +
           sgSignlessShiftedBilinearForm m lambda
            (fun v => x (sgChildVertex m 1 v))
            (fun v => y (sgChildVertex m 1 v)) +
           sgSignlessShiftedBilinearForm m lambda
            (fun v => x (sgChildVertex m 2 v))
            (fun v => y (sgChildVertex m 2 v)) +
           lambda *
            (x (sgParentMidpoint01 m) * y (sgParentMidpoint01 m) +
             x (sgParentMidpoint02 m) * y (sgParentMidpoint02 m) +
             x (sgParentMidpoint12 m) * y (sgParentMidpoint12 m))) := by
    linear_combination
      hDecompSum - hParentPol - hDecompX - hDecompY +
        hChild0Pol + hChild1Pol + hChild2Pol
  linarith


end PhiGenesis.SpectralGap
