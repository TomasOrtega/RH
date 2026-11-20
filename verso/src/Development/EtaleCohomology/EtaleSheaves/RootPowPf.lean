import Development.EtaleCohomology.EtaleSheaves.UliftSmulEq

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.RootPowPf

/- English proof (translation)
Establish `h` using `ζ.2.2`. Rewrite using `[IsRoot.def, ← map_cyclotomic_int q A, Polynomial.eval_map]`. Rewrite `h` using `[aeval_def]`. Conclude with `h`.
-/
theorem prim_eval {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : IsRoot (cyclotomic q A) ζ.1 := by
  have h := ζ.2.2
  rw [IsRoot.def, ← map_cyclotomic_int q A, Polynomial.eval_map]
  rw [aeval_def] at h
  exact h

/- English proof (translation)
Establish `h` using `(prim_eval ζ).dvd (cyclotomic.dvd_X_pow_sub_one q A)`. Simplify `h` using `[IsRoot.def, sub_eq_zero]`.
-/
theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := (prim_eval ζ).dvd (cyclotomic.dvd_X_pow_sub_one q A)
  simpa [IsRoot.def, sub_eq_zero] using h

/- English proof (translation)
Establish `: NeZero (q : K)` using `⟨ζ.2.1.ne_zero⟩`. Establish `: NeZero q` using `NeZero.of_neZero_natCast K`. Establish `hζ : IsPrimitiveRoot ζ.1 q` using `isRoot_cyclotomic_iff.1 (prim_eval ζ)`. Establish `hξ : IsPrimitiveRoot ξ.1 q` using `isRoot_cyclotomic_iff.1 (prim_eval ξ)`. Take `⟨i, hi, he⟩` from `hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one`.

Establish `hc : i.Coprime q` using `(hζ.pow_iff_coprime (NeZero.pos q) i).1 (he ▸ hξ)`. Use `⟨ZMod.unitOfCoprime i hc, ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]`.
-/
theorem field_case {q : ℕ} {K : Type} [Field K] (ζ ξ : Prim q K) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  have : NeZero q := NeZero.of_neZero_natCast K
  have hζ : IsPrimitiveRoot ζ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ζ)
  have hξ : IsPrimitiveRoot ξ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ξ)
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]

/- English proof (translation)
Take `⟨a, ha⟩` from `field_case (ζ.map (IsLocalRing.residue O)) (ξ.map (IsLocalRing.residue O))`. Use `⟨a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsLocalRing.residue O ξ.1 = (IsLocalRing.residue O ζ.1) ^ _ at ha`. Rewrite `ha` using `[← map_pow]`. Use `set η := ζ.1 ^ (a : ZMod q).val with hη`.

Establish `hηq : η ^ q = 1` using `by rw [hη, ← pow_mul, mul_comm, pow_mul, prim_pow, one_pow]`. Establish `hq : q ≠ 0`. Introduce and unpack `rfl`. Use `ζ.2.1` as an intermediate fact. Simplify using `at this`.

Establish `hηu : IsUnit η` using `IsUnit.of_pow_eq_one hηq hq`. Establish `hg` using `(Commute.all ξ.1 η).geom_sum₂_mul q`. Rewrite `hg` using `[prim_pow, hηq, sub_self]`. Establish `hu : IsUnit (∑ i ∈ Finset.range q, ξ.1 ^ i * η ^ (q - 1 - i))`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit]`.

Simplify using `only [map_sum, map_mul, map_pow, ha]`. Rewrite using `[geom_sum₂_self]`. Establish `h1 : IsUnit ((q : O) * η ^ (q - 1))` using `ζ.2.1.mul (hηu.pow _)`. Establish `h2` using `(h1.map (IsLocalRing.residue O)).ne_zero`. Simplify using `using h2`.

Conclude with `sub_eq_zero.1 (hu.mul_right_eq_zero.1 hg)`.
-/
theorem local_case {q : ℕ} {O : Type} [CommRing O] [IsLocalRing O] (ζ ξ : Prim q O) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨a, ha⟩ := field_case (ζ.map (IsLocalRing.residue O)) (ξ.map (IsLocalRing.residue O))
  refine ⟨a, ?_⟩
  change IsLocalRing.residue O ξ.1 = (IsLocalRing.residue O ζ.1) ^ _ at ha
  rw [← map_pow] at ha
  set η := ζ.1 ^ (a : ZMod q).val with hη
  have hηq : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, prim_pow, one_pow]
  have hq : q ≠ 0 := by
    rintro rfl
    have := ζ.2.1
    simp at this
  have hηu : IsUnit η := IsUnit.of_pow_eq_one hηq hq
  have hg := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [prim_pow, hηq, sub_self] at hg
  have hu : IsUnit (∑ i ∈ Finset.range q, ξ.1 ^ i * η ^ (q - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp only [map_sum, map_mul, map_pow, ha]
    rw [geom_sum₂_self]
    have h1 : IsUnit ((q : O) * η ^ (q - 1)) := ζ.2.1.mul (hηu.pow _)
    have h2 := (h1.map (IsLocalRing.residue O)).ne_zero
    simpa using h2
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 hg)

def sv {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : Sieve Y where
  arrows := fun Z g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val
  downward_closed := by
    rintro Z W g ⟨a, ha⟩ h
    refine ⟨a, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _ at ha
    change (h ≫ g).appTop.hom ξ.1 = (h ≫ g).appTop.hom ζ.1 ^ _
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ha, map_pow]

/- English proof (translation)
Take `⟨a, ha⟩` from `local_case (ζ.map (Y.presheaf.germ ⊤ y trivial).hom) (ξ.map (Y.presheaf.germ ⊤ y trivial).hom)`. Express the relevant statement in the definitionally equal form `(Y.presheaf.germ ⊤ y trivial).hom ξ.1 = (Y.presheaf.germ ⊤ y trivial).hom ζ.1 ^ _ at ha`. Rewrite `ha` using `[← map_pow]`. Take `⟨(U : Y.Opens), hU, i, i', he⟩` from `TopCat.Presheaf.germ_eq Y.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ ha`. Use `⟨U, hU, a, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `U.ι.appTop.hom ξ.1 = U.ι.appTop.hom ζ.1 ^ _`. Rewrite using `[← map_pow]`. Establish `hf : U.ι.appTop = Y.presheaf.map i.op ≫ U.topIso.inv`. Rewrite using `[Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]`. Conclude with `(Y.presheaf.map_comp _ _).symm ▸ rfl`.

Establish `hi : i' = i` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Rewrite using `[hf]`. Conclude with `congrArg U.topIso.inv.hom he`.
-/
theorem nhd {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ sv ζ ξ U.ι := by
  obtain ⟨a, ha⟩ := local_case (ζ.map (Y.presheaf.germ ⊤ y trivial).hom) (ξ.map (Y.presheaf.germ ⊤ y trivial).hom)
  change (Y.presheaf.germ ⊤ y trivial).hom ξ.1 = (Y.presheaf.germ ⊤ y trivial).hom ζ.1 ^ _ at ha
  rw [← map_pow] at ha
  obtain ⟨(U : Y.Opens), hU, i, i', he⟩ := TopCat.Presheaf.germ_eq Y.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ ha
  refine ⟨U, hU, a, ?_⟩
  change U.ι.appTop.hom ξ.1 = U.ι.appTop.hom ζ.1 ^ _
  rw [← map_pow]
  have hf : U.ι.appTop = Y.presheaf.map i.op ≫ U.topIso.inv := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact (Y.presheaf.map_comp _ _).symm ▸ rfl
  have hi : i' = i := Subsingleton.elim _ _
  subst hi
  rw [hf]
  exact congrArg U.topIso.inv.hom he

/- English proof (translation)
Apply `Scheme.zariskiTopology_le_etaleTopology` to reduce the goal to its premises. Use `choose U hU hS using nhd ζ ξ`. Use `Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers Y (fun y => (U y : Scheme)) (fun y => (U y).ι) (fun y => ⟨y, ⟨y, hU y⟩, rfl⟩) (fun y => inferInstance), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ _ ⟨y⟩`. Conclude with `hS y`.
-/
theorem sv_mem {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : sv ζ ξ ∈ Scheme.etaleTopology Y := by
  apply Scheme.zariskiTopology_le_etaleTopology
  choose U hU hS using nhd ζ ξ
  refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers Y (fun y => (U y : Scheme)) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hU y⟩, rfl⟩) (fun y => inferInstance), ?_⟩
  rintro _ _ ⟨y⟩
  exact hS y

/- English proof (translation)
Introduce `q Y ζ s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ ξ h => absurd h (Finset.notMem_empty ξ)⟩`. Consider the case `insert ξ s _ ih`. Take `⟨S, hS, h⟩` from `ih`.

Use `⟨S ⊓ sv ζ ξ, GrothendieckTopology.intersection_covering _ hS (sv_mem ζ ξ), ?_⟩` and prove the remaining obligations. Introduce and unpack `Z g ⟨h1, h2⟩ η hη`. Break down `Finset.mem_insert.1 hη with rfl | hη` into its components or cases. Conclude with `h2`. Conclude with `h g h1 η hη`.
-/
theorem RootPow_of : LateralTheory.E.MulPf.RootPow := by
  classical
  intro q Y ζ s
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ ξ h => absurd h (Finset.notMem_empty ξ)⟩
  | insert ξ s _ ih =>
    obtain ⟨S, hS, h⟩ := ih
    refine ⟨S ⊓ sv ζ ξ, GrothendieckTopology.intersection_covering _ hS (sv_mem ζ ξ), ?_⟩
    rintro Z g ⟨h1, h2⟩ η hη
    rcases Finset.mem_insert.1 hη with rfl | hη
    · exact h2
    · exact h g h1 η hη

end LateralTheory.E.RootPowPf
