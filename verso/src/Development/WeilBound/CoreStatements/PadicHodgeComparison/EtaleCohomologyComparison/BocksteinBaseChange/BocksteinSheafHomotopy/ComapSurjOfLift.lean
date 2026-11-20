import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

/- English proof (translation)
Introduce `p`. Set `K` to `AlgebraicClosure p.asIdeal.ResidueField`. Set `ψ : A →+* K` to `(algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)`. Take `⟨χ, hχ⟩` from `h K ψ`. Use `⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `χ (algebraMap A S a) = 0 ↔ a ∈ p.asIdeal`. Rewrite using `[← RingHom.comp_apply, hχ]`. Simplify using `only [ψ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField K).injective]`. Rewrite using `[← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]`.
-/
theorem comap_surj_of_lift {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : A →+* K), ∃ χ : S →+* K, χ.comp (algebraMap A S) = ψ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A S)) := by
  intro p
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let ψ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  obtain ⟨χ, hχ⟩ := h K ψ
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change χ (algebraMap A S a) = 0 ↔ a ∈ p.asIdeal
  rw [← RingHom.comp_apply, hχ]
  simp only [ψ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField K).injective]
  rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

/- English proof (translation)
Set `φ0 : Γ(U, ⊤) ⟶ CommRingCat.of S` to `CommRingCat.ofHom (algebraMap Γ(U, ⊤) S)`. Establish `: Etale (Spec.map φ0)` using `HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)`. Establish `: Surjective (Spec.map φ0)` using `⟨hS⟩`. Establish `: Surjective (pullback.fst U.toSpecΓ (Spec.map φ0))` using `MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance`. Use `⟨pullback U.toSpecΓ (Spec.map φ0), pullback.fst _ _, ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop).hom, ?_, ?_⟩` and prove the remaining obligations.

Set `𝒰 : U.Cover (Scheme.precoverage @Etale)` to `Scheme.Cover.mkOfCovers Unit (fun _ => pullback U.toSpecΓ (Spec.map φ0)) (fun _ => pullback.fst _ _) (fun x => ⟨(), (pullback.fst U.toSpecΓ (Spec.map φ0)).surjective x⟩) (fun _ => inferInstance)`. Conclude with `𝒰.mem_grothendieckTopology`. Introduce `a`. Establish `h` using `congrArg Scheme.Hom.appTop (pullback.condition (f := U.toSpecΓ) (g := Spec.map φ0))`. Rewrite `h` using `[Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]`.

Establish `key : φ0 ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop = (pullback.fst U.toSpecΓ (Spec.map φ0)).appTop`. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso Γ(U, ⊤)).hom, h, ← Category.assoc, ← Scheme.ΓSpecIso_naturality]`. Simplify using `only [Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `congrArg (fun k => k.hom a) key`.
-/
theorem etaleCover (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S))) :
    ∃ (W : Scheme.{0}) (π : W ⟶ U) (φ : S →+* Γ(W, ⊤)),
      Sieve.ofArrows (fun _ : Unit => W) (fun _ => π) ∈ Scheme.etaleTopology U ∧
      ∀ a, φ (algebraMap Γ(U, ⊤) S a) = π.appTop.hom a := by
  let φ0 : Γ(U, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap Γ(U, ⊤) S)
  have : Etale (Spec.map φ0) := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : Surjective (Spec.map φ0) := ⟨hS⟩
  have : Surjective (pullback.fst U.toSpecΓ (Spec.map φ0)) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  refine ⟨pullback U.toSpecΓ (Spec.map φ0), pullback.fst _ _,
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop).hom, ?_, ?_⟩
  · let 𝒰 : U.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers Unit
      (fun _ => pullback U.toSpecΓ (Spec.map φ0)) (fun _ => pullback.fst _ _)
      (fun x => ⟨(), (pullback.fst U.toSpecΓ (Spec.map φ0)).surjective x⟩) (fun _ => inferInstance)
    exact 𝒰.mem_grothendieckTopology
  · intro a
    have h := congrArg Scheme.Hom.appTop (pullback.condition (f := U.toSpecΓ) (g := Spec.map φ0))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
    have key : φ0 ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop =
        (pullback.fst U.toSpecΓ (Spec.map φ0)).appTop := by
      rw [← cancel_epi (Scheme.ΓSpecIso Γ(U, ⊤)).hom, h, ← Category.assoc, ← Scheme.ΓSpecIso_naturality]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun k => k.hom a) key

/- English proof (translation)
Take `⟨W, π, φ, hmem, hφ⟩` from `etaleCover U S hS`. Use `⟨_, hmem, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨_, h, _, ⟨i⟩, rfl⟩` from `hg`. Use `hP V (h ≫ π) (h.appTop.hom.comp φ) fun a => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hφ, Scheme.Hom.comp_appTop]`.

Both sides reduce to the same expression.
-/
theorem loc_of_etale (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S)))
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (χ : S →+* Γ(V, ⊤)), (∀ a, χ (algebraMap Γ(U, ⊤) S a) = g.appTop.hom a) → P V g) :
    Loc U P := by
  obtain ⟨W, π, φ, hmem, hφ⟩ := etaleCover U S hS
  refine ⟨_, hmem, fun V g hg => ?_⟩
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  refine hP V (h ≫ π) (h.appTop.hom.comp φ) fun a => ?_
  rw [RingHom.comp_apply, hφ, Scheme.Hom.comp_appTop]
  rfl

/- English proof (translation)
Break down `Nat.eq_zero_or_pos m with rfl | hm0` into its components or cases. Use `⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨1, ?_⟩⟩` and prove the remaining obligations. Establish `h01 : (0 : Γ(U, ⊤)) = 1` using `by simpa using isUnit_zero_iff.mp (by simpa using hm)`. Establish `h01' : (0 : Γ(V, ⊤)) = 1` using `by simpa using congrArg g.appTop.hom h01`. Use `subsingleton_of_zero_eq_one h01'` as an intermediate fact.

Conclude with `Subsingleton.elim _ _`. Set `c : Γ(U, ⊤)` to `(hm.unit⁻¹ : (Γ(U, ⊤))ˣ)`. Establish `hc : c * (m : Γ(U, ⊤)) = 1` using `hm.val_inv_mul`. Set `Pp : StandardEtalePair Γ(U, ⊤)` to `{ f := X ^ m - C u.1 monic_f := monic_X_pow_sub_C _ hm0.ne' g := X cond := ⟨C c * X, 0, m, by`. Rewrite using `[derivative_sub, derivative_X_pow, derivative_C, sub_zero]`.

Establish `hX : (X : (Γ(U, ⊤))[X]) ^ (m - 1) * X = X ^ m` using `by rw [← pow_succ, Nat.sub_add_cancel hm0]`. Establish `hC : C (m : Γ(U, ⊤)) * C c = 1` using `by rw [← C_mul, mul_comm, hc, C_1]`. Take the linear combination `(X ^ (m - 1) * X) * hC + hX⟩ }`. Use `loc_of_etale U Pp.Ring (comap_surj_of_lift fun K _ _ ψ => ?_) _ fun V g χ hχ => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `IsAlgClosed.exists_pow_nat_eq (ψ u.1) hm0`.

Set `_` to `ψ.toAlgebra`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hx` using `[zero_pow hm0.ne']`. Conclude with `(u.isUnit.map ψ).ne_zero hx.symm`.

Establish `hmap : Pp.HasMap x` using `⟨by simp [Pp, hx, RingHom.algebraMap_toAlgebra], by simpa [Pp] using hx0⟩`. Conclude with `⟨(Pp.lift x hmap).toRingHom, (Pp.lift x hmap).comp_algebraMap⟩`. Use `⟨χ Pp.X, ?_⟩` and prove the remaining obligations. Establish `h0` using `(StandardEtalePair.hasMap_X (P := Pp)).1`. Establish `h1 : Pp.X ^ m = algebraMap Γ(U, ⊤) Pp.Ring u.1`.

Simplify `h0` using `[Pp, sub_eq_zero]`. Rewrite using `[← map_pow, h1, hχ]`.
-/
theorem kumLoc (U : Scheme.{0}) (m : ℕ) (u : (Γ(U, ⊤))ˣ) (hm : IsUnit (m : Γ(U, ⊤))) :
    Loc U fun V g => ∃ v : Γ(V, ⊤), v ^ m = g.appTop.hom u.1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨1, ?_⟩⟩
    have h01 : (0 : Γ(U, ⊤)) = 1 := by simpa using isUnit_zero_iff.mp (by simpa using hm)
    have h01' : (0 : Γ(V, ⊤)) = 1 := by simpa using congrArg g.appTop.hom h01
    have := subsingleton_of_zero_eq_one h01'
    exact Subsingleton.elim _ _
  · let c : Γ(U, ⊤) := (hm.unit⁻¹ : (Γ(U, ⊤))ˣ)
    have hc : c * (m : Γ(U, ⊤)) = 1 := hm.val_inv_mul
    let Pp : StandardEtalePair Γ(U, ⊤) :=
      { f := X ^ m - C u.1
        monic_f := monic_X_pow_sub_C _ hm0.ne'
        g := X
        cond := ⟨C c * X, 0, m, by
          rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
          have hX : (X : (Γ(U, ⊤))[X]) ^ (m - 1) * X = X ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm0]
          have hC : C (m : Γ(U, ⊤)) * C c = 1 := by rw [← C_mul, mul_comm, hc, C_1]
          linear_combination (X ^ (m - 1) * X) * hC + hX⟩ }
    refine loc_of_etale U Pp.Ring (comap_surj_of_lift fun K _ _ ψ => ?_) _ fun V g χ hχ => ?_
    · obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (ψ u.1) hm0
      let _ := ψ.toAlgebra
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_pow hm0.ne'] at hx
        exact (u.isUnit.map ψ).ne_zero hx.symm
      have hmap : Pp.HasMap x := ⟨by simp [Pp, hx, RingHom.algebraMap_toAlgebra], by simpa [Pp] using hx0⟩
      exact ⟨(Pp.lift x hmap).toRingHom, (Pp.lift x hmap).comp_algebraMap⟩
    · refine ⟨χ Pp.X, ?_⟩
      have h0 := (StandardEtalePair.hasMap_X (P := Pp)).1
      have h1 : Pp.X ^ m = algebraMap Γ(U, ⊤) Pp.Ring u.1 := by
        simpa [Pp, sub_eq_zero] using h0
      rw [← map_pow, h1, hχ]

/- English proof (translation)
Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (NeZero.ne m)`. Set `c : Γ(U, ⊤)` to `(hm.unit⁻¹ : (Γ(U, ⊤))ˣ)`. Establish `hc : c * (m : Γ(U, ⊤)) = 1` using `hm.val_inv_mul`. Take `⟨h, hh⟩` from `cyclotomic.dvd_X_pow_sub_one m Γ(U, ⊤)`. Set `Pp : StandardEtalePair Γ(U, ⊤)` to `{ f := cyclotomic m Γ(U, ⊤) monic_f := cyclotomic.monic m Γ(U, ⊤) g := X cond := ⟨C c * X * h, C c * X * derivative h, m, by`.

Establish `hd` using `congrArg derivative hh`. Rewrite `hd` using `[derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul]`. Establish `hX : (X : (Γ(U, ⊤))[X]) * X ^ (m - 1) = X ^ m` using `by rw [← pow_succ', Nat.sub_add_cancel hm0]`. Establish `hC : C c * C (m : Γ(U, ⊤)) = 1` using `by rw [← C_mul, hc, C_1]`. Take the linear combination `(C c * X) * hd.symm + (X * X ^ (m - 1)) * hC + hX⟩ }`.

Use `loc_of_etale U Pp.Ring (comap_surj_of_lift fun K _ _ ψ => ?_) _ fun V g χ hχ => ?_` and prove the remaining obligations. Set `_` to `ψ.toAlgebra`. Establish `hdeg : (cyclotomic m K).degree ≠ 0`. Rewrite using `[degree_cyclotomic]`. Conclude with `(Nat.totient_pos.2 hm0).ne'` after adjusting the coercions.

Take `⟨x, hx⟩` from `IsAlgClosed.exists_root _ hdeg`. Establish `hx1 : x ^ m = 1`. Take `⟨k, hk⟩` from `cyclotomic.dvd_X_pow_sub_one m K`. Use `congrArg (eval x) hk` as an intermediate fact. Rewrite `this` using `[eval_sub, eval_pow, eval_X, eval_one, eval_mul, hx.eq_zero, zero_mul, sub_eq_zero]`.

Conclude with `this`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hx1` using `[zero_pow hm0.ne']`. Conclude with `zero_ne_one hx1`.

Establish `hmap : Pp.HasMap x` using `⟨by`. Express the relevant statement in the definitionally equal form `aeval x (cyclotomic m Γ(U, ⊤)) = 0`. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `hx.eq_zero, by simpa [Pp] using hx0⟩`. Conclude with `⟨(Pp.lift x hmap).toRingHom, (Pp.lift x hmap).comp_algebraMap⟩`.

Use `⟨⟨χ Pp.X, ?_, ?_⟩⟩` and prove the remaining obligations. Establish `: IsUnit ((m : ℕ) : Γ(V, ⊤))` using `by simpa using hm.map g.appTop.hom`. Conclude with `this`. Establish `h0 : aeval Pp.X (cyclotomic m Γ(U, ⊤)) = 0` using `(StandardEtalePair.hasMap_X (P := Pp)).1`. Establish `h2 : aeval Pp.X (cyclotomic m ℤ) = 0`.

Rewrite `h0` using `[← map_cyclotomic_int, ← algebraMap_int_eq, aeval_map_algebraMap]`. Conclude with `h0`. Establish `h3` using `Polynomial.aeval_algHom_apply χ.toIntAlgHom Pp.X (cyclotomic m ℤ)`. Rewrite `h3` using `[h2, map_zero]`. Conclude with `h3`.
-/
theorem primLoc (U : Scheme.{0}) (m : ℕ) [NeZero m] (hm : IsUnit (m : Γ(U, ⊤))) :
    Loc U fun V _ => Nonempty (Prim m Γ(V, ⊤)) := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let c : Γ(U, ⊤) := (hm.unit⁻¹ : (Γ(U, ⊤))ˣ)
  have hc : c * (m : Γ(U, ⊤)) = 1 := hm.val_inv_mul
  obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one m Γ(U, ⊤)
  let Pp : StandardEtalePair Γ(U, ⊤) :=
    { f := cyclotomic m Γ(U, ⊤)
      monic_f := cyclotomic.monic m Γ(U, ⊤)
      g := X
      cond := ⟨C c * X * h, C c * X * derivative h, m, by
        have hd := congrArg derivative hh
        rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at hd
        have hX : (X : (Γ(U, ⊤))[X]) * X ^ (m - 1) = X ^ m := by rw [← pow_succ', Nat.sub_add_cancel hm0]
        have hC : C c * C (m : Γ(U, ⊤)) = 1 := by rw [← C_mul, hc, C_1]
        linear_combination (C c * X) * hd.symm + (X * X ^ (m - 1)) * hC + hX⟩ }
  refine loc_of_etale U Pp.Ring (comap_surj_of_lift fun K _ _ ψ => ?_) _ fun V g χ hχ => ?_
  · let _ := ψ.toAlgebra
    have hdeg : (cyclotomic m K).degree ≠ 0 := by
      rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hm0).ne'
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    have hx1 : x ^ m = 1 := by
      obtain ⟨k, hk⟩ := cyclotomic.dvd_X_pow_sub_one m K
      have := congrArg (eval x) hk
      rw [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hx.eq_zero, zero_mul, sub_eq_zero] at this
      exact this
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0.ne'] at hx1
      exact zero_ne_one hx1
    have hmap : Pp.HasMap x := ⟨by
        change aeval x (cyclotomic m Γ(U, ⊤)) = 0
        rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
        exact hx.eq_zero, by simpa [Pp] using hx0⟩
    exact ⟨(Pp.lift x hmap).toRingHom, (Pp.lift x hmap).comp_algebraMap⟩
  · refine ⟨⟨χ Pp.X, ?_, ?_⟩⟩
    · have : IsUnit ((m : ℕ) : Γ(V, ⊤)) := by simpa using hm.map g.appTop.hom
      exact this
    · have h0 : aeval Pp.X (cyclotomic m Γ(U, ⊤)) = 0 := (StandardEtalePair.hasMap_X (P := Pp)).1
      have h2 : aeval Pp.X (cyclotomic m ℤ) = 0 := by
        rw [← map_cyclotomic_int, ← algebraMap_int_eq, aeval_map_algebraMap] at h0
        exact h0
      have h3 := Polynomial.aeval_algHom_apply χ.toIntAlgHom Pp.X (cyclotomic m ℤ)
      rw [h2, map_zero] at h3
      exact h3

end CrystallineSemistableComparison.KummerTwistLemmas
