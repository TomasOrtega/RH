import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongOff

open Matrix
open scoped TensorProduct

variable {D : D7}

/- English proof (translation)
Establish `hsep : ∀ u ∈ S, ∃ x : 𝓞 D.host.F, x ∈ u.asIdeal ∧ x ∉ v.asIdeal`. Introduce `u hu`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `e : u.asIdeal = v.asIdeal` using `u.isMaximal.eq_of_le v.isPrime.ne_top hn`.

Conclude with `hv (HeightOneSpectrum.ext e ▸ hu)`. Use `choose! x hx hxv using hsep`. Establish `hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ u ∈ S, x u) ∈ 𝔪.radical`. Rewrite using `[Ideal.radical_eq_sInf]`. Use `Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_` and prove the remaining obligations.

Establish `hJ0 : J ≠ ⊥` using `fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))`. Set `Q : HeightOneSpectrum (𝓞 D.host.E)` to `⟨J, hJp, hJ0⟩`. Establish `hu` using `hS Q hJ`. Establish `hxu : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J` using `hx _ hu`. Rewrite using `[map_prod, ← Finset.prod_erase_mul _ _ hu]`.

Conclude with `Ideal.mul_mem_left J _ hxu`. Take `⟨K, hK⟩` from `hz`. Use `⟨(∏ u ∈ S, x u) ^ K, by rwa [map_pow], fun h => ?_⟩` and prove the remaining obligations. Establish `h1` using `v.isPrime.mem_of_pow_mem K h`. Take `⟨u, hu, h2⟩` from `(v.isPrime.prod_mem_iff).1 h1`.

Conclude with `hxv u hu h2`.
-/
theorem exists_F_mem_not_mem {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ S) :
    ∃ X : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∈ 𝔪 ∧ X ∉ v.asIdeal := by
  classical
  have hsep : ∀ u ∈ S, ∃ x : 𝓞 D.host.F, x ∈ u.asIdeal ∧ x ∉ v.asIdeal := by
    intro u hu
    by_contra hn
    push_neg at hn
    have e : u.asIdeal = v.asIdeal := u.isMaximal.eq_of_le v.isPrime.ne_top hn
    exact hv (HeightOneSpectrum.ext e ▸ hu)
  choose! x hx hxv using hsep
  have hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ u ∈ S, x u) ∈ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))
    let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJp, hJ0⟩
    have hu := hS Q hJ
    have hxu : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J := hx _ hu
    rw [map_prod, ← Finset.prod_erase_mul _ _ hu]
    exact Ideal.mul_mem_left J _ hxu
  obtain ⟨K, hK⟩ := hz
  refine ⟨(∏ u ∈ S, x u) ^ K, by rwa [map_pow], fun h => ?_⟩
  have h1 := v.isPrime.mem_of_pow_mem K h
  obtain ⟨u, hu, h2⟩ := (v.isPrime.prod_mem_iff).1 h1
  exact hxv u hu h2

end GlobalTheory.CongOff

namespace GlobalTheory.CongOff
open Matrix
open scoped TensorProduct

section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Establish `h1 : Valued.v (algebraMap F (v.adicCompletion F) (X : F)) = 1`. Use `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v X` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hX]`. Conclude with `this`. Use `⟨?_, fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1⟩` and prove the remaining obligations.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]`.
-/
theorem unit_int' {v : HeightOneSpectrum (𝓞 F)} {X : 𝓞 F} (hX : X ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (X : F))⁻¹ ∈ v.adicCompletionIntegers F ∧
    algebraMap F (v.adicCompletion F) (X : F) ≠ 0 := by
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) (X : F)) = 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v X
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hX] at this
    exact this
  refine ⟨?_, fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

/- English proof (translation)
Take `⟨hint, hne⟩` from `unit_int' hXv`. Introduce `y hy`. Use `GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _) (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy` and prove the remaining obligations. Establish `hm` using `Submodule.smul_mem_smul hX𝔪 hx`. Establish `h3 : a * (algebraMap F (v.adicCompletion F) (X : F))⁻¹ ∈ v.adicCompletionIntegers F` using `mul_mem ha hint`.

Establish `h2` using `GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) h3 hm`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Establish `e : (algebraMap (𝓞 F) (𝓞 E) X • x) i = (X : F) • x i`. Rewrite using `[Pi.smul_apply, Algebra.smul_def (X : F)]`.

Both sides reduce to the same expression. Rewrite using `[e, ← TensorProduct.smul_tmul, Algebra.smul_def]`. Use `congr 1`. Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel₀ hne, mul_one]`.
-/
theorem latLoc_le_smul_of (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {v : HeightOneSpectrum (𝓞 F)}
    (X : 𝓞 F) (hX𝔪 : algebraMap (𝓞 F) (𝓞 E) X ∈ 𝔪) (hXv : X ∉ v.asIdeal) :
    GlobalTheory.AdelicU.latLoc F Λ v ≤ GlobalTheory.AdelicU.latLoc F (𝔪 • Λ) v := by
  obtain ⟨hint, hne⟩ := unit_int' hXv
  intro y hy
  refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _) (fun _ _ h h' => add_mem h h')
    (fun _ h => neg_mem h) hy
  have hm := Submodule.smul_mem_smul hX𝔪 hx
  have h3 : a * (algebraMap F (v.adicCompletion F) (X : F))⁻¹ ∈ v.adicCompletionIntegers F := mul_mem ha hint
  have h2 := GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) h3 hm
  convert h2 using 1
  funext i
  have e : (algebraMap (𝓞 F) (𝓞 E) X • x) i = (X : F) • x i := by
    rw [Pi.smul_apply, Algebra.smul_def (X : F)]
    rfl
  rw [e, ← TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ hne, mul_one]
end General
end GlobalTheory.CongOff

namespace GlobalTheory.CongOff
open Matrix
open scoped TensorProduct

/- English proof (translation)
Establish `: Module.Finite R N` using `Module.Finite.iff_fg.2 hN`. Establish `: IsNoetherian R N` using `isNoetherian_of_isNoetherianRing_of_finite R N`. Establish `h` using `(IsNoetherian.noetherian ((I • N).comap N.subtype))`. Establish `e : ((I • N).comap N.subtype).map N.subtype = I • N` using `Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact Submodule.smul_le_right)`. Rewrite using `[← e]`.

Conclude with `h.map _`.
-/
theorem fg_ideal_smul {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (N : Submodule R M) (hN : N.FG) : (I • N).FG := by
  have : Module.Finite R N := Module.Finite.iff_fg.2 hN
  have : IsNoetherian R N := isNoetherian_of_isNoetherianRing_of_finite R N
  have h := (IsNoetherian.noetherian ((I • N).comap N.subtype))
  have e : ((I • N).comap N.subtype).map N.subtype = I • N :=
    Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact Submodule.smul_le_right)
  rw [← e]; exact h.map _

variable {D : D7}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `y hy`. Take `⟨y', rfl⟩ : ∃ y' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) = y` from `⟨fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose, funext fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose_spec⟩`. Establish `hy'` using `(GlobalTheory.LevSplit.latHat_iff _ y').2 hy`. Establish `e : (Lev.finE V g).1 *ᵥ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) - (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) = fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - …`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.sub_apply, Pi.sub_apply, map_sub]`. Use `congr 1`. Conclude with `(RingHom.map_mulVec (GlobalTheory.LevSplit.swp D.host.F D.host.E) (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) y' i).symm`. Rewrite using `[e, ← GlobalTheory.LevSplit.latHat_iff, GlobalTheory.AdelicU.mem_latHat_iff (fg_ideal_smul 𝔪 _ (GlobalTheory.AdelicU.frameLat_fg V))]`. Introduce `v`.

Establish `hv` using `(GlobalTheory.AdelicU.mem_latHat_iff (GlobalTheory.AdelicU.frameLat_fg V) y').1 hy' v`. Rewrite using `[show GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - y') = GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y') - GlobalTheory.AdelicU.vecLoc v y' from`. Use function extensionality and compare the values at `fun i => map_sub _ _ _, GlobalTheory.AdelicU.vecLoc_mulVec]`. Distinguish the cases in `hvS : v ∈ S`. Rewrite using `[hon v hvS, map_one, Units.val_one, Matrix.one_mulVec, sub_self]`.

Conclude with `zero_mem _`. Take `⟨X, hX𝔪, hXv⟩` from `exists_F_mem_not_mem h𝔪 hS hvS`. Conclude with `latLoc_le_smul_of _ 𝔪 X hX𝔪 hXv (sub_mem ((GlobalTheory.AdelicU.mem_stabLoc.1 (hoff v hvS) _).1 hv) hv)`.
-/
theorem cong_fin {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) (V : HSp D) (g : GA D V)
    (hoff : ∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v)
    (hon : ∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g = 1) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.AdelicU.frameLat V),
      (Lev.finE V g).1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • GlobalTheory.AdelicU.frameLat V) := by
  intro y hy
  obtain ⟨y', rfl⟩ : ∃ y' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) = y :=
    ⟨fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose, funext fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose_spec⟩
  have hy' := (GlobalTheory.LevSplit.latHat_iff _ y').2 hy
  have e : (Lev.finE V g).1 *ᵥ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) -
      (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) =
      fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - y') i) := by
    funext i
    rw [Pi.sub_apply, Pi.sub_apply, map_sub]
    congr 1
    exact (RingHom.map_mulVec (GlobalTheory.LevSplit.swp D.host.F D.host.E) (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) y' i).symm
  rw [e, ← GlobalTheory.LevSplit.latHat_iff,
    GlobalTheory.AdelicU.mem_latHat_iff (fg_ideal_smul 𝔪 _ (GlobalTheory.AdelicU.frameLat_fg V))]
  intro v
  have hv := (GlobalTheory.AdelicU.mem_latHat_iff (GlobalTheory.AdelicU.frameLat_fg V) y').1 hy' v
  rw [show GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - y') =
      GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y') - GlobalTheory.AdelicU.vecLoc v y' from
      funext fun i => map_sub _ _ _, GlobalTheory.AdelicU.vecLoc_mulVec]
  by_cases hvS : v ∈ S
  · rw [hon v hvS, map_one, Units.val_one, Matrix.one_mulVec, sub_self]; exact zero_mem _
  · obtain ⟨X, hX𝔪, hXv⟩ := exists_F_mem_not_mem h𝔪 hS hvS
    exact latLoc_le_smul_of _ 𝔪 X hX𝔪 hXv
      (sub_mem ((GlobalTheory.AdelicU.mem_stabLoc.1 (hoff v hvS) _).1 hv) hv)

end GlobalTheory.CongOff

namespace GlobalTheory.CongOff

/- English proof (translation)
Introduce `D V S 𝔪 h𝔪 hS k _ hoff hon`. Use `GlobalTheory.CongMember.mem_congLev_of D.sp.cm V.gram _ 𝔪 _ (GlobalTheory.LevSplit.finE_mem_UA V k) (cong_fin h𝔪 hS V k hoff hon) ?_` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `cong_fin h𝔪 hS V k⁻¹ (fun v hv => by rw [map_inv]; exact inv_mem (hoff v hv)) (fun v hv => by rw [map_inv, hon v hv, inv_one])`.
-/
theorem finE_mem_congLev_of_off : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) → ∀ k : GA D V, k ∈ GfC V → (∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v) → (∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = 1) → Lev.finE V k ∈ congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) 𝔪 := by
  intro D V S 𝔪 h𝔪 hS k _ hoff hon
  refine GlobalTheory.CongMember.mem_congLev_of D.sp.cm V.gram _ 𝔪 _ (GlobalTheory.LevSplit.finE_mem_UA V k)
    (cong_fin h𝔪 hS V k hoff hon) ?_
  rw [← map_inv]
  exact cong_fin h𝔪 hS V k⁻¹ (fun v hv => by rw [map_inv]; exact inv_mem (hoff v hv))
    (fun v hv => by rw [map_inv, hon v hv, inv_one])

end GlobalTheory.CongOff
