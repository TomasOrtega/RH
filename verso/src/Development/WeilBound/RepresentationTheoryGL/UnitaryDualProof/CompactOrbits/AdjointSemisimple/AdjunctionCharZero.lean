import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep

namespace PositivityTheory.RgUd.T.AdjPf

open Module PositivityTheory.RgUd.T

/- English proof (translation)
Use `haveI : IsReduced Z := hr`. Use `letI : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2) }`. Use `haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z`. Use `haveI : IsSemisimpleRing Z := IsArtinianRing.isSemisimpleRing_of_isReduced Z`. Use `haveI : IsSemisimpleModule Z (Fin n → k) := inferInstance`.

Establish `key : ∀ g : Module.End Z (Fin n → k), ∀ v : Fin n → k, Matrix.mulVec x (g v) = g (Matrix.mulVec x v)`. Introduce `g v`. Use `set y := LinearMap.toMatrix' (g.restrictScalars k) with hydef`. Establish `hyv : ∀ w, Matrix.mulVec y w = g w` using `fun w => by`. Rewrite using `[← Matrix.toLin'_apply, hydef, Matrix.toLin'_toMatrix']`.

Both sides reduce to the same expression. Establish `hy : y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce `a ha`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hyv, hyv]`. Conclude with `(g.map_smul ⟨a, ha⟩ w).symm`. Rewrite using `[← hyv, ← hyv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hx y hy]`.

Set `f : Module.End (Module.End Z (Fin n → k)) (Fin n → k)` to `{ toFun := fun v => Matrix.mulVec x v map_add' := Matrix.mulVec_add x map_smul' := fun g v => key g v }`. Take `⟨r, hr'⟩` from `jacobson_density (R := Z) f (Finset.univ.image (fun i : Fin n => (Pi.single i (1 : k) : Fin n → k)))`. Establish `hxr : x = (r : Matrix (Fin n) (Fin n) k)`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.toLin'_apply]`. Conclude with `hr' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Rewrite using `[hxr]`. Conclude with `r.2`.
-/
theorem dc {k : Type} [Field k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hr : IsReduced Z) (x : Matrix (Fin n) (Fin n) k)
    (hx : ∀ y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)), x * y = y * x) : x ∈ Z := by
  classical
  haveI : IsReduced Z := hr
  letI : CommRing Z := { (inferInstance : Ring Z) with
    mul_comm := fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  haveI : IsSemisimpleRing Z := IsArtinianRing.isSemisimpleRing_of_isReduced Z
  haveI : IsSemisimpleModule Z (Fin n → k) := inferInstance
  have key : ∀ g : Module.End Z (Fin n → k), ∀ v : Fin n → k,
      Matrix.mulVec x (g v) = g (Matrix.mulVec x v) := by
    intro g v
    set y := LinearMap.toMatrix' (g.restrictScalars k) with hydef
    have hyv : ∀ w, Matrix.mulVec y w = g w := fun w => by
      rw [← Matrix.toLin'_apply, hydef, Matrix.toLin'_toMatrix']
      rfl
    have hy : y ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro a ha
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro w
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hyv, hyv]
      exact (g.map_smul ⟨a, ha⟩ w).symm
    rw [← hyv, ← hyv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hx y hy]
  let f : Module.End (Module.End Z (Fin n → k)) (Fin n → k) :=
    { toFun := fun v => Matrix.mulVec x v
      map_add' := Matrix.mulVec_add x
      map_smul' := fun g v => key g v }
  obtain ⟨r, hr'⟩ := jacobson_density (R := Z) f
    (Finset.univ.image (fun i : Fin n => (Pi.single i (1 : k) : Fin n → k)))
  have hxr : x = (r : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Matrix.toLin'_apply]
    exact hr' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [hxr]
  exact r.2

/- English proof (translation)
Use `set w : Z := ⟨z, hz⟩ with hw`. Establish `hint : IsIntegral k w` using `IsIntegral.of_finite k w`. Establish `hm0 : minpoly k w ≠ 0` using `minpoly.ne_zero hint`. Use `Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := minpoly k w) ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Take `⟨r, hr⟩` from `hx`. Establish `h1 : Polynomial.aeval w (x * r) = 0`. Apply `IsReduced.eq_zero` to reduce the goal to its premises. Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two, ← map_mul]`.

Establish `hsq : x * r * (x * r) = minpoly k w * r` using `by rw [hr]; ring`. Rewrite using `[hsq, map_mul, minpoly.aeval, zero_mul]`. Establish `h2 : minpoly k w ∣ x * r` using `minpoly.dvd k w h1`. Establish `hxr : x * r ≠ 0`. Introduce `h`.

Apply `hm0` to reduce the goal to its premises. Rewrite using `[hr, mul_assoc, h, mul_zero]`. Rewrite `h2` using `[hr, mul_assoc]`. Establish `h3 : x * (x * r) ∣ 1 * (x * r)` using `by rwa [one_mul]`. Conclude with `isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxr).mp h3)`.

Establish `h0 : Polynomial.aeval z (minpoly k w) = 0`. Establish `h` using `congrArg Z.val (minpoly.aeval k w)`. Rewrite `h` using `[map_zero, ← Polynomial.aeval_algHom_apply]`. Then use the resulting hypothesis. Establish `h4` using `Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom z (minpoly k w)`. Rewrite `h4` using `[h0, map_zero]`.

Conclude with `h4`.
-/
theorem isSemisimple_of_mem {k : Type} [Field k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (hr : IsReduced Z) (z : Matrix (Fin n) (Fin n) k) (hz : z ∈ Z) :
    Module.End.IsSemisimple (Matrix.toLin' z) := by
  set w : Z := ⟨z, hz⟩ with hw
  have hint : IsIntegral k w := IsIntegral.of_finite k w
  have hm0 : minpoly k w ≠ 0 := minpoly.ne_zero hint
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := minpoly k w) ?_ ?_
  · intro x hx
    obtain ⟨r, hr⟩ := hx
    have h1 : Polynomial.aeval w (x * r) = 0 := by
      apply IsReduced.eq_zero
      refine ⟨2, ?_⟩
      rw [pow_two, ← map_mul]
      have hsq : x * r * (x * r) = minpoly k w * r := by rw [hr]; ring
      rw [hsq, map_mul, minpoly.aeval, zero_mul]
    have h2 : minpoly k w ∣ x * r := minpoly.dvd k w h1
    have hxr : x * r ≠ 0 := by
      intro h
      apply hm0
      rw [hr, mul_assoc, h, mul_zero]
    rw [hr, mul_assoc] at h2
    have h3 : x * (x * r) ∣ 1 * (x * r) := by rwa [one_mul]
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxr).mp h3)
  · have h0 : Polynomial.aeval z (minpoly k w) = 0 := by
      have h := congrArg Z.val (minpoly.aeval k w)
      rwa [map_zero, ← Polynomial.aeval_algHom_apply] at h
    have h4 := Polynomial.aeval_algHom_apply
      (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom z (minpoly k w)
    rw [h0, map_zero] at h4
    exact h4

end PositivityTheory.RgUd.T.AdjPf

namespace PositivityTheory.RgUd.T

open Module

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `n Z hZ s hs hsZ hss`. Take `⟨hc, hr⟩` from `hZ`. Use `set S : Set (Matrix (Fin n) (Fin n) k) := insert s (Z : Set (Matrix (Fin n) (Fin n) k)) with hSdef`. Establish `hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a`. Introduce and unpack `a (rfl | ha) b (rfl | hb)`.

Both sides reduce to the same expression. Conclude with `(hs b hb).symm`. Conclude with `hs a ha`. Conclude with `hc a ha b hb`. Establish `hSc : S ⊆ Subalgebra.centralizer k S` using `fun a ha => (Subalgebra.mem_centralizer_iff k).mpr fun g hg => hS g hg a ha`.

Establish `hcomm : ∀ a ∈ adj Z s, ∀ b ∈ adj Z s, a * b = b * a`. Introduce `a ha b hb`. Establish `ha' : a ∈ Subalgebra.centralizer k S` using `Algebra.adjoin_le hSc ha`. Establish `hb' : b ∈ Subalgebra.centralizer k (Subalgebra.centralizer k S : Set (Matrix (Fin n) (Fin n) k))` using `Algebra.adjoin_le_centralizer_centralizer k S hb`. Conclude with `(Subalgebra.mem_centralizer_iff k).mp hb' a ha'`.

Establish `hsemi : ∀ x ∈ adj Z s, Module.End.IsSemisimple (Matrix.toLin' x)`. Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | hx` into its components or cases.

Conclude with `hss`. Conclude with `AdjPf.isSemisimple_of_mem Z hr x hx`. Consider the case `algebraMap r`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one]`. Conclude with `Module.End.IsSemisimple_smul r Module.End.isSemisimple_id`.

Consider the case `add x y hx hy ihx ihy`. Establish `hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y)`. Express the relevant statement in the definitionally equal form `Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x`. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm x hx y hy]`. Rewrite using `[map_add]`.

Conclude with `Module.End.IsSemisimple.add_of_commute hcm ihx ihy`. Consider the case `mul x y hx hy ihx ihy`. Establish `hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y)`. Express the relevant statement in the definitionally equal form `Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x`. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm x hx y hy]`.

Rewrite using `[Matrix.toLin'_mul, ← Module.End.mul_eq_comp]`. Conclude with `Module.End.IsSemisimple.mul_of_commute hcm ihx ihy`. Use `⟨⟨hcomm, ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxs` using `hsemi x.1 x.2`.

Establish `hn : IsNilpotent (Matrix.toLin' (x : Matrix (Fin n) (Fin n) k))`. Take `⟨m, hm⟩` from `hx`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hm' : (x : Matrix (Fin n) (Fin n) k) ^ m = 0`. Rewrite using `[← Subalgebra.coe_pow, hm, Subalgebra.coe_zero]`.

Establish `h5` using `congrArg (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) hm'`. Rewrite `h5` using `[map_pow, map_zero]`. Conclude with `h5`. Establish `h6` using `Module.End.eq_zero_of_isNilpotent_isSemisimple hn hxs`. Conclude with `Subtype.ext ((Matrix.toLin'.map_eq_zero_iff).mp h6)`.

Establish `hsub : (Z : Set (Matrix (Fin n) (Fin n) k)) ⊆ (adj Z s : Set (Matrix (Fin n) (Fin n) k))` using `fun z hz => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)`. Establish `hle` using `Subalgebra.centralizer_le k _ _ hsub`. Establish `hne : Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k)) ≠ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))`. Introduce `h`. Apply `hsZ` to reduce the goal to its premises.

Apply `AdjPf.dc Z hc hr s` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[← h]`. Conclude with `(Subalgebra.mem_centralizer_iff k).mp hy s (Algebra.subset_adjoin (Set.mem_insert _ _))`. Establish `hlt : Subalgebra.toSubmodule (Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k))) < Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))` using `lt_of_le_of_ne (Subalgebra.toSubmodule.monotone hle) (fun h => hne (Subalgebra.toSubmodule_injective h))`.

Conclude with `Submodule.finrank_lt_finrank_of_lt hlt`.
-/
theorem adjunction_char_zero [CharZero k] : Adj (k := k) := by
  intro n Z hZ s hs hsZ hss
  obtain ⟨hc, hr⟩ := hZ
  set S : Set (Matrix (Fin n) (Fin n) k) := insert s (Z : Set (Matrix (Fin n) (Fin n) k)) with hSdef
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (rfl | ha) b (rfl | hb)
    · rfl
    · exact (hs b hb).symm
    · exact hs a ha
    · exact hc a ha b hb
  have hSc : S ⊆ Subalgebra.centralizer k S := fun a ha =>
    (Subalgebra.mem_centralizer_iff k).mpr fun g hg => hS g hg a ha
  have hcomm : ∀ a ∈ adj Z s, ∀ b ∈ adj Z s, a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ Subalgebra.centralizer k S := Algebra.adjoin_le hSc ha
    have hb' : b ∈ Subalgebra.centralizer k (Subalgebra.centralizer k S : Set (Matrix (Fin n) (Fin n) k)) :=
      Algebra.adjoin_le_centralizer_centralizer k S hb
    exact (Subalgebra.mem_centralizer_iff k).mp hb' a ha'
  have hsemi : ∀ x ∈ adj Z s, Module.End.IsSemisimple (Matrix.toLin' x) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hss
      · exact AdjPf.isSemisimple_of_mem Z hr x hx
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one]
      exact Module.End.IsSemisimple_smul r Module.End.isSemisimple_id
    | add x y hx hy ihx ihy =>
      have hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y) := by
        change Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          ← Matrix.toLin'_mul, hcomm x hx y hy]
      rw [map_add]
      exact Module.End.IsSemisimple.add_of_commute hcm ihx ihy
    | mul x y hx hy ihx ihy =>
      have hcm : Commute (Matrix.toLin' x) (Matrix.toLin' y) := by
        change Matrix.toLin' x * Matrix.toLin' y = Matrix.toLin' y * Matrix.toLin' x
        rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
          ← Matrix.toLin'_mul, hcomm x hx y hy]
      rw [Matrix.toLin'_mul, ← Module.End.mul_eq_comp]
      exact Module.End.IsSemisimple.mul_of_commute hcm ihx ihy
  refine ⟨⟨hcomm, ?_⟩, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    have hxs := hsemi x.1 x.2
    have hn : IsNilpotent (Matrix.toLin' (x : Matrix (Fin n) (Fin n) k)) := by
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      have hm' : (x : Matrix (Fin n) (Fin n) k) ^ m = 0 := by
        rw [← Subalgebra.coe_pow, hm, Subalgebra.coe_zero]
      have h5 := congrArg (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) hm'
      rw [map_pow, map_zero] at h5
      exact h5
    have h6 := Module.End.eq_zero_of_isNilpotent_isSemisimple hn hxs
    exact Subtype.ext ((Matrix.toLin'.map_eq_zero_iff).mp h6)
  · have hsub : (Z : Set (Matrix (Fin n) (Fin n) k)) ⊆ (adj Z s : Set (Matrix (Fin n) (Fin n) k)) :=
      fun z hz => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)
    have hle := Subalgebra.centralizer_le k _ _ hsub
    have hne : Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k)) ≠
        Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
      intro h
      apply hsZ
      apply AdjPf.dc Z hc hr s
      intro y hy
      rw [← h] at hy
      exact (Subalgebra.mem_centralizer_iff k).mp hy s (Algebra.subset_adjoin (Set.mem_insert _ _))
    have hlt : Subalgebra.toSubmodule (Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k))) <
        Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
      lt_of_le_of_ne (Subalgebra.toSubmodule.monotone hle)
        (fun h => hne (Subalgebra.toSubmodule_injective h))
    exact Submodule.finrank_lt_finrank_of_lt hlt

end PositivityTheory.RgUd.T
