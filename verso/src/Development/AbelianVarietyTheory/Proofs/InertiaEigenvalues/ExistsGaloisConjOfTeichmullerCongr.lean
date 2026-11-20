import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOfCompatibleRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystemsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveMapIntegersClToWittQuotientStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Rewrite using `[GlobalTheory.RingBasics.mem_OC]`. Establish `h1` using `(GlobalTheory.RingBasics.mem_OC _).1 c.2`. Rewrite `h1` using `[← h, norm_pow]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1`.
-/
theorem mem_OC_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : ℂ_[l]) (c : OC l)
    (h : a ^ N = (c : ℂ_[l])) : a ∈ 𝓞_ℂ_[l] := by
  rw [GlobalTheory.RingBasics.mem_OC]
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 c.2
  rw [← h, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

/- English proof (translation)
Take `⟨a, ha⟩` from `IsAlgClosed.exists_pow_nat_eq (c : ℂ_[l]) hN`. Use `haveI : NeZero (N : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] N`. Set `a' : OC l` to `⟨a, mem_OC_of_pow_eq hN a c ha⟩`.

Set `ζ' : OC l` to `⟨ζ, mem_OC_of_pow_eq hN ζ 1 hζ.pow_eq_one⟩`. Establish `hζ' : IsPrimitiveRoot ζ' N` using `IsPrimitiveRoot.of_map_of_injective (f := (𝓞_ℂ_[l]).subtype) hζ Subtype.val_injective`. Establish `ha' : a' ^ N = c` using `Subtype.ext ha`. Establish `hp` using `congrArg (Polynomial.eval₂ f r) (X_pow_sub_C_eq_prod hζ' hN ha')`. Rewrite `hp` using `[Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h, sub_self, eq_comm, Finset.prod_eq_zero_iff]`.

Take `⟨i, -, hi⟩` from `hp`. Rewrite `hi` using `[Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]`. Conclude with `⟨_, hi.symm⟩`.
-/
theorem exists_OC_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] (f : OC l →+* D)
    {N : ℕ} (hN : 0 < N) (c : OC l) (r : D) (h : r ^ N = f c) : ∃ s : OC l, f s = r := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ_[l]) hN
  haveI : NeZero (N : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] N
  let a' : OC l := ⟨a, mem_OC_of_pow_eq hN a c ha⟩
  let ζ' : OC l := ⟨ζ, mem_OC_of_pow_eq hN ζ 1 hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' N :=
    IsPrimitiveRoot.of_map_of_injective (f := (𝓞_ℂ_[l]).subtype) hζ Subtype.val_injective
  have ha' : a' ^ N = c := Subtype.ext ha
  have hp := congrArg (Polynomial.eval₂ f r) (X_pow_sub_C_eq_prod hζ' hN ha')
  rw [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h,
    sub_self, eq_comm, Finset.prod_eq_zero_iff] at hp
  obtain ⟨i, -, hi⟩ := hp
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hi
  exact ⟨_, hi.symm⟩

/- English proof (translation)
Establish `hf : (Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)) ≠ 0` using `Polynomial.X_pow_sub_C_ne_zero hN a`. Establish `hroot : ((Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)).map (algebraMap (Om l) ℂ_[l])).IsRoot s`. Simplify using `only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]`. Rewrite using `[h]`. Conclude with `sub_self _`.

Take `⟨z, hz⟩` from `(IsAlgClosed.splits _).mem_range_of_isRoot hf hroot`. Conclude with `⟨z, hz.symm⟩`.
-/
theorem exists_alg_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : Om l) (s : ℂ_[l])
    (h : s ^ N = (a : ℂ_[l])) : ∃ z : Om l, s = (z : ℂ_[l]) := by
  have hf : (Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hN a
  have hroot : ((Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)).map
      (algebraMap (Om l) ℂ_[l])).IsRoot s := by
    simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [h]
    exact sub_self _
  obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
  exact ⟨z, hz.symm⟩

/- English proof (translation)
Establish `hp : ∀ (n : ℕ) (x : O), (((frobeniusEquiv O l).symm)^[n] x) ^ (l ^ n) = x`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ n ih => intro x`. Rewrite using `[Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]`. Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus' (I := Ideal.span {c}) _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Establish `h1` using `pow_dvd_pow_of_dvd (h n) (l ^ n)`. Rewrite `h1` using `[sub_pow_char_pow, hp, hp]`. Conclude with `(pow_dvd_pow c (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans h1`.
-/
theorem eq_of_forall_dvd_root_sub {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : O) [IsHausdorff (Ideal.span {c}) O] (v w : O)
    (h : ∀ n : ℕ, c ∣ ((frobeniusEquiv O l).symm)^[n] v - ((frobeniusEquiv O l).symm)^[n] w) : v = w := by
  have hp : ∀ (n : ℕ) (x : O), (((frobeniusEquiv O l).symm)^[n] x) ^ (l ^ n) = x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {c}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h1 := pow_dvd_pow_of_dvd (h n) (l ^ n)
  rw [sub_pow_char_pow, hp, hp] at h1
  exact (pow_dvd_pow c (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans h1

/- English proof (translation)
Introduce `l _ K bk O _ _ _ _ _ ψ h0 hu hc v hv`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Take `⟨f, hf, hinj, hdom, hmod⟩` from `GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc`. Take `⟨hprime, hπ⟩` from `GlobalTheory.T.breuilKisin_prime_uniformizer_class l K bk`. Take `⟨halg, hfix⟩` from `GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk`.

Use `set π : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) with hπd`. Establish `hft : ∀ y : OCb l, f y.untilt = Ideal.Quotient.mk _ (WittVector.teichmuller l (ψ y))` using `fun y => by`. Rewrite using `[← WittVector.fontaineTheta_teichmuller, ← WittVector.map_teichmuller]`. Conclude with `hf _`. Set `r : ℕ → WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}` to `fun n => Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v))`.

Establish `hr0 : r 0 = f bk.flat.untilt`. Rewrite using `[hft]`. Conclude with `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hv)`. Establish `hrs : ∀ n, r (n + 1) ^ l = r n` using `fun n => by`. Simplify using `only [r]`.

Rewrite using `[← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]`. Establish `hrn : ∀ n, r n ^ (l ^ n) = f bk.flat.untilt` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_one, hr0]`. Consider the case `succ n ih => rw [pow_succ', pow_mul, hrs, ih]`.

Use `choose s hs using fun n => exists_OC_eq_of_pow_eq f (pow_pos hl n) _ _ (hrn n)`. Establish `hss : ∀ n, s (n + 1) ^ l = s n` using `fun n => hinj (by rw [map_pow, hs, hs, hrs])`. Establish `hsn : ∀ n, s n ^ (l ^ n) = bk.flat.untilt` using `fun n => hinj (by rw [map_pow, hs, hrn])`. Establish `hπc : ((bk.flat.untilt : OC l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])`. Rewrite using `[← hπ, coe_intToOC]`.

Establish `hcoe : Function.Injective (fun z : Om l => (z : ℂ_[l]))` using `(algebraMap (Om l) ℂ_[l]).injective`. Establish `hcp : ∀ (z : Om l) (m : ℕ), ((z ^ m : Om l) : ℂ_[l]) = (z : ℂ_[l]) ^ m` using `fun z m => map_pow (algebraMap (Om l) ℂ_[l]) z m`. Use `choose z hz using fun n => exists_alg_eq_of_pow_eq (pow_pos hl n) ((π : ↥K.1) : Om l) (s n : ℂ_[l]) (by rw [← hπc, ← hsn n, SubmonoidClass.coe_pow])`. Use `choose y hy using halg`. Establish `hts : ∀ n, GlobalTheory.MemLoc.rootT bk.flat (n + 1) ^ l = GlobalTheory.MemLoc.rootT bk.flat n` using `fun n => by`.

Rewrite using `[GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]`. Take `⟨g, hg⟩` from `GlobalTheory.T.galois_transitive_on_prime_power_root_systems l K π hprime y z (hcoe (by`. Express the relevant statement in the definitionally equal form `((y 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])`. Rewrite using `[← hy, ← hπc]`. Use the proof step `rfl))`.

Use the proof step `(hcoe (by`. Express the relevant statement in the definitionally equal form `((z 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])`. Rewrite using `[← hz, ← hπc, ← hsn 0, pow_zero, pow_one]))`. Use the proof step `(fun n => hcoe (by`. Express the relevant statement in the definitionally equal form `((y (n + 1) ^ l : Om l) : ℂ_[l]) = ((y n : Om l) : ℂ_[l])`.

Rewrite using `[hcp, ← hy, ← hy, ← hts n, SubmonoidClass.coe_pow]))`. Use the proof step `(fun n => hcoe (by`. Express the relevant statement in the definitionally equal form `((z (n + 1) ^ l : Om l) : ℂ_[l]) = ((z n : Om l) : ℂ_[l])`. Rewrite using `[hcp, ← hz, ← hz, ← hss n, SubmonoidClass.coe_pow]))`. Take `⟨w, hw⟩` from `GlobalTheory.tilt_of_compatible_roots l s hss`.

Establish `hgw : Per.σF (g : GQ l) bk.flat = w` using `hfix _ _ fun n => Subtype.ext (by`. Use `(GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_` and prove the remaining obligations. Rewrite using `[hy, hw, hz, ← hg n]`. Conclude with `GlobalTheory.RingBasics.σC_coe _ _)`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Rewrite using `[hgw]`. Use `eq_of_forall_dvd_root_sub (l := l) (ψ bk.flat) v (ψ w) fun n => ?_` and prove the remaining obligations. Establish `hψ : ∀ m, ψ (((frobeniusEquiv (OCb l) l).symm)^[m] w) = ((frobeniusEquiv O l).symm)^[m] (ψ w)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => rfl`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, RingHom.map_frobeniusEquiv_symm]`. Establish `h1` using `hft (((frobeniusEquiv (OCb l) l).symm)^[n] w)`. Establish `h2 : f (s n) = Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w)))`.

Rewrite using `[← hw n, ← hψ]`. Conclude with `h1`. Establish `h3` using `hmod (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v) - WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w))) (by rw [map_sub, ← h2, hs, sub_self]; exact dvd_zero _)`. Rewrite `h3` using `[← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]`. Conclude with `(dvd_pow_self _ bk.deg_pos.ne').trans h3`.
-/
theorem exists_gal_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc v hv
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨f, hf, hinj, hdom, hmod⟩ := GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc
  obtain ⟨hprime, hπ⟩ := GlobalTheory.T.breuilKisin_prime_uniformizer_class l K bk
  obtain ⟨halg, hfix⟩ := GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk
  set π : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) with hπd
  have hft : ∀ y : OCb l, f y.untilt = Ideal.Quotient.mk _ (WittVector.teichmuller l (ψ y)) := fun y => by
    rw [← WittVector.fontaineTheta_teichmuller, ← WittVector.map_teichmuller]
    exact hf _
  let r : ℕ → WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)} := fun n =>
    Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v))
  have hr0 : r 0 = f bk.flat.untilt := by
    rw [hft]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hv)
  have hrs : ∀ n, r (n + 1) ^ l = r n := fun n => by
    simp only [r]
    rw [← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  have hrn : ∀ n, r n ^ (l ^ n) = f bk.flat.untilt := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_one, hr0]
    | succ n ih => rw [pow_succ', pow_mul, hrs, ih]
  choose s hs using fun n => exists_OC_eq_of_pow_eq f (pow_pos hl n) _ _ (hrn n)
  have hss : ∀ n, s (n + 1) ^ l = s n := fun n => hinj (by rw [map_pow, hs, hs, hrs])
  have hsn : ∀ n, s n ^ (l ^ n) = bk.flat.untilt := fun n => hinj (by rw [map_pow, hs, hrn])
  have hπc : ((bk.flat.untilt : OC l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← hπ, coe_intToOC]
  have hcoe : Function.Injective (fun z : Om l => (z : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hcp : ∀ (z : Om l) (m : ℕ), ((z ^ m : Om l) : ℂ_[l]) = (z : ℂ_[l]) ^ m :=
    fun z m => map_pow (algebraMap (Om l) ℂ_[l]) z m
  choose z hz using fun n => exists_alg_eq_of_pow_eq (pow_pos hl n) ((π : ↥K.1) : Om l) (s n : ℂ_[l])
    (by rw [← hπc, ← hsn n, SubmonoidClass.coe_pow])
  choose y hy using halg
  have hts : ∀ n, GlobalTheory.MemLoc.rootT bk.flat (n + 1) ^ l = GlobalTheory.MemLoc.rootT bk.flat n := fun n => by
    rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  obtain ⟨g, hg⟩ := GlobalTheory.T.galois_transitive_on_prime_power_root_systems l K π hprime y z
    (hcoe (by
      change ((y 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hy, ← hπc]
      rfl))
    (hcoe (by
      change ((z 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hz, ← hπc, ← hsn 0, pow_zero, pow_one]))
    (fun n => hcoe (by
      change ((y (n + 1) ^ l : Om l) : ℂ_[l]) = ((y n : Om l) : ℂ_[l])
      rw [hcp, ← hy, ← hy, ← hts n, SubmonoidClass.coe_pow]))
    (fun n => hcoe (by
      change ((z (n + 1) ^ l : Om l) : ℂ_[l]) = ((z n : Om l) : ℂ_[l])
      rw [hcp, ← hz, ← hz, ← hss n, SubmonoidClass.coe_pow]))
  obtain ⟨w, hw⟩ := GlobalTheory.tilt_of_compatible_roots l s hss
  have hgw : Per.σF (g : GQ l) bk.flat = w := hfix _ _ fun n => Subtype.ext (by
    refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
    rw [hy, hw, hz, ← hg n]
    exact GlobalTheory.RingBasics.σC_coe _ _)
  refine ⟨g, ?_⟩
  rw [hgw]
  refine eq_of_forall_dvd_root_sub (l := l) (ψ bk.flat) v (ψ w) fun n => ?_
  have hψ : ∀ m, ψ (((frobeniusEquiv (OCb l) l).symm)^[m] w) = ((frobeniusEquiv O l).symm)^[m] (ψ w) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, RingHom.map_frobeniusEquiv_symm]
  have h1 := hft (((frobeniusEquiv (OCb l) l).symm)^[n] w)
  have h2 : f (s n) = Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w))) := by
    rw [← hw n, ← hψ]
    exact h1
  have h3 := hmod (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v) -
      WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w)))
    (by rw [map_sub, ← h2, hs, sub_self]; exact dvd_zero _)
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h3
  exact (dvd_pow_self _ bk.deg_pos.ne').trans h3

end GlobalTheory.BSP
