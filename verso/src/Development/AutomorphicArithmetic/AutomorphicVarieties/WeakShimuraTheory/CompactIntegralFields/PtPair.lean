import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.TriSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GenTri
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.SmallFlag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Rewrite `hv` using `[hq.1.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finset_sum, add_eq_zero_iff_eq_neg]`. Use `Ideal.IsPrime.mem_of_pow_mem inferInstance q.natDegree ?_` and prove the remaining obligations. Rewrite using `[hv]`. Use `neg_mem (Ideal.sum_mem _ fun n hn => ?_)` and prove the remaining obligations. Rewrite using `[eval₂_mul, eval₂_C]`.

Conclude with `Ideal.mul_mem_right _ _ (hf _ (hq.2 n (Finset.mem_range.1 hn)))`.
-/
private theorem ptp_root {B V : Type} [CommRing B] [CommRing V] [IsLocalRing V] (f : B →+* V) {I : Ideal B}
    (hf : ∀ b ∈ I, f b ∈ maximalIdeal V) {q : B[X]} (hq : Pp.Dist I q) {v : V} (hv : q.eval₂ f v = 0) :
    v ∈ maximalIdeal V := by
  rw [hq.1.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finset_sum, add_eq_zero_iff_eq_neg] at hv
  refine Ideal.IsPrime.mem_of_pow_mem inferInstance q.natDegree ?_
  rw [hv]
  refine neg_mem (Ideal.sum_mem _ fun n hn => ?_)
  rw [eval₂_mul, eval₂_C]
  exact Ideal.mul_mem_right _ _ (hf _ (hq.2 n (Finset.mem_range.1 hn)))

/- English proof (translation)
Introduce `_ Ω _ _ _ l _ c D hD 𝔞 r ⟨hs, R, _, _, _, ρ, y, hρ, hy, hm, hr⟩`. Substitute `hr` using the available equality. Establish `hy' : ∀ a, y (algebraMap c.O R a) = 𝔞.a c a` using `fun a => DFunLike.congr_fun hy a`. Take `⟨B, _, _, _, _, τ, hτ, ⟨x, hx⟩, z, hz⟩` from `hρ.atL`. Take `⟨-, -, -, -, -, hrev, hinj, -⟩` from `facts D hD`.

Use `haveI : HenselianLocalRing B := GlobalTheory.henselianLocalRing_of_henselianRing B`. Take `⟨h, P, H, hP, hI⟩` from `Pp.genTri ((D.Ip l).subgroupOf (D.Gp l)) (fun i (g : D.Gp l) => (D.ps i g : c.O)) D.s0 (D.th D.s0 : c.O) τ.hom x hD.decompSigma_mem.1.1 hinj (fun i => by rw [← hrev i]; rfl) (Units.ne_zero _) (hτ.1 _) hτ.2 hx`. Set `f : B →+* 𝔞.V` to `y.comp (z : B →+* R)`. Take `⟨h', H'⟩` from `Pp.triSpec _ P _ (𝔞.V.subtype.comp f) h (fun a ha => by`. Rewrite `ha` using `[RingHom.mem_ker, map_eq_zero_iff _ (IsFractionRing.injective B (FractionRing B))]`.

Rewrite using `[ha]`. Conclude with `zero_mem _) H`. Take `⟨u, hu, U⟩` from `Pp.triIwa 𝔞.V _ P f h' H'`. Establish `hf : ∀ a, f (algebraMap c.O B a) = 𝔞.a c a` using `fun a => (congrArg y (z.commutes a)).trans (hy' a)`. Establish `hfm : ∀ b ∈ maximalIdeal B, f b ∈ maximalIdeal 𝔞.V` using `fun b hb => hm _ ((res_eq_zero_iff c.O R _).1 ((res_map z b).trans ((res_eq_zero_iff c.O B _).2 hb)))`.

Establish `e : ∀ s : D.Gp l, (τ.hom s).map f = mapRep y ρ.hom s` using `fun s => by`. Establish `: (D.loc ρ l).hom s = ρ.hom s` using `rfl`. Use extensionality with `i j`. Rewrite using `[mapRep_apply, ← this, ← hz]`. Both sides reduce to the same expression.

Use `⟨u, Pp.smallFlag 𝔞 _ u hs, fun g i j => ?_, fun g => ?_, fun A hA g hg hb => ?_, fun p hp g hg => ?_, hu, fun s hs => ?_, fun s hs i => ?_, fun s hs i => ?_⟩` and prove the remaining obligations. Rewrite using `[mapRep_apply, ← hy', ← map_sub]`. Use `hm _ ((res_eq_zero_iff c.O R _).1 ?_)` and prove the remaining obligations. Rewrite using `[map_sub, ρ.red, AlgHom.commutes]`. Conclude with `sub_self _`.

Establish `h1` using `hρ.mult g`. Unfold `IsGSp at h1 ⊢`. Use `show adj ((ρ.hom g).map y) * (ρ.hom g).map y = _`. Rewrite using `[(grp R).2.2.2.2.2.1, ← Matrix.map_mul, h1, ← hy']`. Use extensionality with `i j`.

Rewrite using `[Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Matrix.one_apply, Matrix.one_apply, apply_ite y, map_one, map_zero]`. Use `show y.mapMatrix (ρ.hom g) = 1`. Rewrite using `[hρ.unr A hA g hg hb, map_one]`. Take `⟨B', _, _, _, _, τ', hτ', -, z', hz'⟩` from `hρ.atP p hp`. Establish `h1 : ρ.hom g = (D.loc ρ p).hom ⟨g, hg.1.1⟩` using `rfl`.

Use `show y.mapMatrix (ρ.hom g) = 1`. Rewrite using `[h1, ← hz']`. Use `show y.mapMatrix (z'.mapMatrix (τ'.hom _)) = 1`. Rewrite using `[hτ'.2 _ hg, map_one, map_one]`. Use `(U ⟨s, hs⟩).1` as an intermediate fact.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Take `⟨q, hq, hq'⟩` from `hP ⟨s, hs⟩ i`. Use `(U ⟨s, hs⟩).2 i` as an intermediate fact. Rewrite `this` using `[e, hq', eval₂_comp, eval₂_sub, eval₂_X, eval₂_C, hf]`. Conclude with `ptp_root f hfm hq this`.

Use `(U ⟨s, hs.1⟩).2 i` as an intermediate fact. Rewrite `this` using `[e, hI _ hs, eval₂_sub, eval₂_X, eval₂_C, hf]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem UpperTheory.V.Ws.ptPair :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r, VPt D 𝔞 r → ∃ u, KPair D 𝔞 r u := by
  intro _ Ω _ _ _ l _ c D hD 𝔞 r ⟨hs, R, _, _, _, ρ, y, hρ, hy, hm, hr⟩
  subst hr
  have hy' : ∀ a, y (algebraMap c.O R a) = 𝔞.a c a := fun a => DFunLike.congr_fun hy a
  obtain ⟨B, _, _, _, _, τ, hτ, ⟨x, hx⟩, z, hz⟩ := hρ.atL
  obtain ⟨-, -, -, -, -, hrev, hinj, -⟩ := facts D hD
  haveI : HenselianLocalRing B := GlobalTheory.henselianLocalRing_of_henselianRing B
  obtain ⟨h, P, H, hP, hI⟩ := Pp.genTri ((D.Ip l).subgroupOf (D.Gp l)) (fun i (g : D.Gp l) => (D.ps i g : c.O)) D.s0
    (D.th D.s0 : c.O) τ.hom x hD.decompSigma_mem.1.1 hinj (fun i => by rw [← hrev i]; rfl) (Units.ne_zero _) (hτ.1 _) hτ.2 hx
  let f : B →+* 𝔞.V := y.comp (z : B →+* R)
  obtain ⟨h', H'⟩ := Pp.triSpec _ P _ (𝔞.V.subtype.comp f) h (fun a ha => by
    rw [RingHom.mem_ker, map_eq_zero_iff _ (IsFractionRing.injective B (FractionRing B))] at ha
    rw [ha]
    exact zero_mem _) H
  obtain ⟨u, hu, U⟩ := Pp.triIwa 𝔞.V _ P f h' H'
  have hf : ∀ a, f (algebraMap c.O B a) = 𝔞.a c a := fun a => (congrArg y (z.commutes a)).trans (hy' a)
  have hfm : ∀ b ∈ maximalIdeal B, f b ∈ maximalIdeal 𝔞.V := fun b hb =>
    hm _ ((res_eq_zero_iff c.O R _).1 ((res_map z b).trans ((res_eq_zero_iff c.O B _).2 hb)))
  have e : ∀ s : D.Gp l, (τ.hom s).map f = mapRep y ρ.hom s := fun s => by
    have : (D.loc ρ l).hom s = ρ.hom s := rfl
    ext i j
    rw [mapRep_apply, ← this, ← hz]
    rfl
  refine ⟨u, Pp.smallFlag 𝔞 _ u hs, fun g i j => ?_, fun g => ?_, fun A hA g hg hb => ?_, fun p hp g hg => ?_, hu,
    fun s hs => ?_, fun s hs i => ?_, fun s hs i => ?_⟩
  · rw [mapRep_apply, ← hy', ← map_sub]
    refine hm _ ((res_eq_zero_iff c.O R _).1 ?_)
    rw [map_sub, ρ.red, AlgHom.commutes]
    exact sub_self _
  · have h1 := hρ.mult g
    unfold IsGSp at h1 ⊢
    show adj ((ρ.hom g).map y) * (ρ.hom g).map y = _
    rw [(grp R).2.2.2.2.2.1, ← Matrix.map_mul, h1, ← hy']
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Matrix.one_apply,
      Matrix.one_apply, apply_ite y, map_one, map_zero]
  · show y.mapMatrix (ρ.hom g) = 1
    rw [hρ.unr A hA g hg hb, map_one]
  · obtain ⟨B', _, _, _, _, τ', hτ', -, z', hz'⟩ := hρ.atP p hp
    have h1 : ρ.hom g = (D.loc ρ p).hom ⟨g, hg.1.1⟩ := rfl
    show y.mapMatrix (ρ.hom g) = 1
    rw [h1, ← hz']
    show y.mapMatrix (z'.mapMatrix (τ'.hom _)) = 1
    rw [hτ'.2 _ hg, map_one, map_one]
  · have := (U ⟨s, hs⟩).1
    rwa [e] at this
  · obtain ⟨q, hq, hq'⟩ := hP ⟨s, hs⟩ i
    have := (U ⟨s, hs⟩).2 i
    rw [e, hq', eval₂_comp, eval₂_sub, eval₂_X, eval₂_C, hf] at this
    exact ptp_root f hfm hq this
  · have := (U ⟨s, hs.1⟩).2 i
    rw [e, hI _ hs, eval₂_sub, eval₂_X, eval₂_C, hf] at this
    exact sub_eq_zero.1 this
