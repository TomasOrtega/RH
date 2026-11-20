import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.WeakApproxPI
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieLat

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Adic

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `U : Set (v.adicCompletion F)` to `(fun x => c⁻¹ * (x - y)) ⁻¹' ((v.adicCompletionIntegers F) : Set (v.adicCompletion F))`. Establish `hU : IsOpen U` using `(Valued.isOpen_integer (v.adicCompletion F)).preimage (continuous_const.mul (continuous_id.sub continuous_const))`. Establish `hU' : U.Nonempty` using `⟨y, by`. Simplify using `only [U, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]`. Conclude with `zero_mem _⟩`.

Take `⟨a, ha⟩` from `(HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (v := v)).exists_mem_open hU hU'`. Use `⟨a, _, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hc, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adic_dense (v : HeightOneSpectrum (𝓞 F)) (y c : v.adicCompletion F) (hc : c ≠ 0) :
    ∃ a : F, ∃ z ∈ v.adicCompletionIntegers F, algebraMap F (v.adicCompletion F) a = y + c * z := by
  let U : Set (v.adicCompletion F) :=
    (fun x => c⁻¹ * (x - y)) ⁻¹' ((v.adicCompletionIntegers F) : Set (v.adicCompletion F))
  have hU : IsOpen U := (Valued.isOpen_integer (v.adicCompletion F)).preimage
    (continuous_const.mul (continuous_id.sub continuous_const))
  have hU' : U.Nonempty := ⟨y, by
    simp only [U, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
    exact zero_mem _⟩
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (v := v)).exists_mem_open hU hU'
  refine ⟨a, _, ha, ?_⟩
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  ring

/- English proof (translation)
Establish `hb : ∃ b ∈ v'.asIdeal, b ∉ v.asIdeal`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hle : v'.asIdeal ≤ v.asIdeal` using `fun b hb => hcon b hb`. Conclude with `h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle)).symm`.

Take `⟨b, hb', hb⟩` from `hb`. Establish `hb0 : algebraMap (𝓞 F) F b ≠ 0`. Introduce `h0`. Establish `: b = 0` using `(FaithfulSMul.algebraMap_injective (𝓞 F) F) (by rw [h0, map_zero])`. Conclude with `hb (this ▸ v.asIdeal.zero_mem)`.

Use `⟨(algebraMap (𝓞 F) F b)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b)⁻¹) = v.valuation F (algebraMap (𝓞 F) F b)⁻¹` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v _`. Rewrite using `[e, map_inv₀]`. Establish `h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1` using `le_antisymm (v.valuation_le_one b) (not_lt.1 fun hlt => hb ((v.valuation_lt_one_iff_mem (K := F) b).1 hlt))`.

Rewrite using `[h1, inv_one]`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e : Valued.v (algebraMap F (v'.adicCompletion F) (algebraMap (𝓞 F) F b)⁻¹) = v'.valuation F (algebraMap (𝓞 F) F b)⁻¹` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v' _`. Rewrite using `[e, map_inv₀, not_le]`. Establish `h1 : v'.valuation F (algebraMap (𝓞 F) F b) < 1` using `(v'.valuation_lt_one_iff_mem (K := F) b).2 hb'`.

Establish `h2 : v'.valuation F (algebraMap (𝓞 F) F b) ≠ 0` using `(Valuation.ne_zero_iff _).2 hb0`. Conclude with `(one_lt_inv₀ (zero_lt_iff.2 h2)).2 h1`.
-/
theorem adic_dist (v v' : HeightOneSpectrum (𝓞 F)) (h : v ≠ v') :
    ∃ a : F, algebraMap F (v.adicCompletion F) a ∈ v.adicCompletionIntegers F ∧
      algebraMap F (v'.adicCompletion F) a ∉ v'.adicCompletionIntegers F := by
  have hb : ∃ b ∈ v'.asIdeal, b ∉ v.asIdeal := by
    by_contra hcon
    push Not at hcon
    have hle : v'.asIdeal ≤ v.asIdeal := fun b hb => hcon b hb
    exact h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle)).symm
  obtain ⟨b, hb', hb⟩ := hb
  have hb0 : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h0
    have : b = 0 := (FaithfulSMul.algebraMap_injective (𝓞 F) F) (by rw [h0, map_zero])
    exact hb (this ▸ v.asIdeal.zero_mem)
  refine ⟨(algebraMap (𝓞 F) F b)⁻¹, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b)⁻¹) =
        v.valuation F (algebraMap (𝓞 F) F b)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v _
    rw [e, map_inv₀]
    have h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1 :=
      le_antisymm (v.valuation_le_one b) (not_lt.1 fun hlt => hb ((v.valuation_lt_one_iff_mem (K := F) b).1 hlt))
    rw [h1, inv_one]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : Valued.v (algebraMap F (v'.adicCompletion F) (algebraMap (𝓞 F) F b)⁻¹) =
        v'.valuation F (algebraMap (𝓞 F) F b)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v' _
    rw [e, map_inv₀, not_le]
    have h1 : v'.valuation F (algebraMap (𝓞 F) F b) < 1 := (v'.valuation_lt_one_iff_mem (K := F) b).2 hb'
    have h2 : v'.valuation F (algebraMap (𝓞 F) F b) ≠ 0 := (Valuation.ne_zero_iff _).2 hb0
    exact (one_lt_inv₀ (zero_lt_iff.2 h2)).2 h1

end Adic

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ}

/- English proof (translation)
Establish `hp : ∀ v, ((p : ℕ) : G.P.Qq v) ≠ 0`. Introduce `v h0`. Establish `hS` using `G.P.setting v`. Use `hS.frac_alt` as an intermediate fact. Establish `h1 : algebraMap (G.P.W v) (G.P.Qq v) ((p : ℕ) : G.P.W v) = 0`.

Rewrite using `[map_natCast]`. Conclude with `h0`. Conclude with `hS.p_unif.ne_zero ((IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (by rw [h1, map_zero]))`. Use `weakApprox_of_approx_and_separation G A.iw (fun v => (G.P.setting v).frac_alt) hp (fun v => (G.P.setting v).p_unif.not_isUnit) ?_ ?_` and prove the remaining obligations. Introduce `v x N`.

Establish `hc : (((p : ℕ) : (A.pl v).1.adicCompletion F)) ^ N ≠ 0`. Use `pow_ne_zero _ ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (A.eQ v)]`. Conclude with `(map_ne_zero_iff _ (A.eQ v).injective).2 (hp v)`. Take `⟨a, z, hz, e⟩` from `adic_dense (A.pl v).1 (A.eQ v x) _ hc`.

Take `⟨c, hcc⟩` from `(hW v ((A.eQ v).symm z)).2 (by rw [RingEquiv.apply_symm_apply]; exact hz)`. Use `⟨algebraMap F E a, c, ?_⟩` and prove the remaining obligations. Rewrite using `[hF, e, map_add, map_mul, map_pow, RingEquiv.symm_apply_apply, hcc, map_natCast]`. Introduce `v v' hne`. Take `⟨a, h1, h2⟩` from `adic_dist (A.pl v).1 (A.pl v').1 (fun h => hne (A.pl.injective (Subtype.ext h)))`.

Use `⟨algebraMap F E a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hF]`. Use `(hW v _).2 ?_` and prove the remaining obligations. Rewrite using `[RingEquiv.apply_symm_apply]`. Conclude with `h1`.

Rewrite using `[hF]`. Introduce `hm`. Establish `h3` using `(hW v' _).1 hm`. Rewrite `h3` using `[RingEquiv.apply_symm_apply]`. Conclude with `h2 h3`.
-/
theorem weak_of_locAt (G : GAtP p) (A : LocAt F E n G)
    (hF : ∀ v (a : F), A.iw v (algebraMap F E a) = (A.eQ v).symm (algebraMap F ((A.pl v).1.adicCompletion F) a))
    (hW : ∀ v (x : G.P.Qq v), x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔
      A.eQ v x ∈ (A.pl v).1.adicCompletionIntegers F) : WeakApprox G A.iw := by
  have hp : ∀ v, ((p : ℕ) : G.P.Qq v) ≠ 0 := by
    intro v h0
    have hS := G.P.setting v
    have := hS.frac_alt
    have h1 : algebraMap (G.P.W v) (G.P.Qq v) ((p : ℕ) : G.P.W v) = 0 := by
      rw [map_natCast]; exact h0
    exact hS.p_unif.ne_zero ((IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (by rw [h1, map_zero]))
  refine weakApprox_of_approx_and_separation G A.iw (fun v => (G.P.setting v).frac_alt) hp (fun v => (G.P.setting v).p_unif.not_isUnit) ?_ ?_
  · intro v x N
    have hc : (((p : ℕ) : (A.pl v).1.adicCompletion F)) ^ N ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [← map_natCast (A.eQ v)]
      exact (map_ne_zero_iff _ (A.eQ v).injective).2 (hp v)
    obtain ⟨a, z, hz, e⟩ := adic_dense (A.pl v).1 (A.eQ v x) _ hc
    obtain ⟨c, hcc⟩ := (hW v ((A.eQ v).symm z)).2 (by rw [RingEquiv.apply_symm_apply]; exact hz)
    refine ⟨algebraMap F E a, c, ?_⟩
    rw [hF, e, map_add, map_mul, map_pow, RingEquiv.symm_apply_apply, hcc, map_natCast]
  · intro v v' hne
    obtain ⟨a, h1, h2⟩ := adic_dist (A.pl v).1 (A.pl v').1 (fun h => hne (A.pl.injective (Subtype.ext h)))
    refine ⟨algebraMap F E a, ?_, ?_⟩
    · rw [hF]
      refine (hW v _).2 ?_
      rw [RingEquiv.apply_symm_apply]; exact h1
    · rw [hF]
      intro hm
      have h3 := (hW v' _).1 hm
      rw [RingEquiv.apply_symm_apply] at h3
      exact h2 h3

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

/- English proof (translation)
The claim follows from `congrArg ((locAt X u w hg B).eQ v).symm ((X.g u w hg).spl_F _ ((X.g u w hg).pl v).2 a)`.
-/
theorem locAt_iw_F (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (v : Fin (D.gat u w hg).P.nV) (a : D.host.F) :
    (locAt X u w hg B).iw v (algebraMap D.host.F D.host.E a) =
      ((locAt X u w hg B).eQ v).symm (algebraMap D.host.F (((locAt X u w hg B).pl v).1.adicCompletion D.host.F) a) :=
  congrArg ((locAt X u w hg B).eQ v).symm ((X.g u w hg).spl_F _ ((X.g u w hg).pl v).2 a)

/- English proof (translation)
Introduce `u w hg` and use `weak_of_locAt (D.gat u w hg) (locAt X u w hg I.B) (locAt_iw_F u w hg I.B) (fun v x => (X.g u w hg).completion_integers_iff v _ rfl x)`.
-/
theorem weakRec_pf (I : CmpIn D X) : WeakRec I := fun u w hg =>
  weak_of_locAt (D.gat u w hg) (locAt X u w hg I.B) (locAt_iw_F u w hg I.B) (fun v x => (X.g u w hg).completion_integers_iff v _ rfl x)

variable {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

/- English proof (translation)
The claim follows from `latM_rec H hG hloc hsurj (weakRec_pf I) u w hg`.
-/
theorem latM_rec' (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I)
    (hsurj : SurjRat T Gt I)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).O
      (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M :=
  latM_rec H hG hloc hsurj (weakRec_pf I) u w hg

end Formalism.L2.G
