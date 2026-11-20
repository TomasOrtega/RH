import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite

open Set Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section

namespace PositivityTheory.Rg.Rs.diffstep

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Use `set U' : Set (AdelicGLn.FiniteAdelicGL K n) := Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))`. Establish `hU' : IsOpen U'` using `(AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU`. Establish `h1U' : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ U'` using `⟨1, U.one_mem, rfl⟩`. Use `set Cf : Set (AdelicGLn.FiniteAdelicGL K n) := (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => (AdelicGLn.prodEquiv K n (p.1 * p.2)).2) '' (ω ×ˢ Q)`. Establish `hCf : IsCompact Cf` using `(hω.prod hQ).image (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp (continuous_fst.mul continuous_snd)))`.

Establish `hcont : Continuous fun q : (UPos n r → FiniteAdeleRing (𝓞 K) K) × AdelicGLn.FiniteAdelicGL K n => q.2⁻¹ * unipGL q.1 * q.2` using `(continuous_snd.inv.mul (continuous_unipGL'.comp continuous_fst)).mul continuous_snd`. Establish `hev : ∀ᶠ w in 𝓝 (0 : UPos n r → FiniteAdeleRing (𝓞 K) K), ∀ c ∈ Cf, c⁻¹ * unipGL w * c ∈ U'`. Use `hCf.eventually_forall_of_forall_eventually fun c _ => ?_` and prove the remaining obligations. Use `(hcont.tendsto ((0 : UPos n r → FiniteAdeleRing (𝓞 K) K), c)).eventually (hU'.mem_nhds ?_)` and prove the remaining obligations. Simplify using `only [unipGL_zero, mul_one, inv_mul_cancel]`.

Conclude with `h1U'`. Rewrite `hev` using `[nhds_pi]`. Establish `hev' : {w : UPos n r → FiniteAdeleRing (𝓞 K) K | ∀ c ∈ Cf, c⁻¹ * unipGL w * c ∈ U'} ∈ Filter.pi fun _ => 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)` using `hev`. Rewrite `hev'` using `[Filter.mem_pi]`. Take `⟨I, -, tt, htt, hIt⟩` from `hev'`.

Take `⟨M, hM, hMW⟩` from `exists_natCast_mul_mem_of_mem_nhds K (Filter.iInter_mem.2 htt)`. Use `⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩` and prove the remaining obligations. Use `set w : UPos n r → FiniteAdeleRing (𝓞 K) K := fun p => (z p).2`. Establish `hw : w ∈ I.pi tt` using `fun p _ => by`. Take `⟨a, ha, hza⟩` from `hz2 p`.

Use `hMW a ha` as an intermediate fact. Rewrite `this` using `[mem_iInter]`. Express the relevant statement in the definitionally equal form `(z p).2 ∈ tt p`. Rewrite using `[hza]`. Conclude with `this p`.

Use `set c := (AdelicGLn.prodEquiv K n (b * k)).2`. Establish `hc : c ∈ Cf` using `⟨(b, k), ⟨hb, hk⟩, rfl⟩`. Take `⟨u, huU, hu⟩` from `hIt hw c hc`. Use `⟨⟨u, huU⟩, ?_⟩` and prove the remaining obligations. Apply `(AdelicGLn.prodEquiv K n).injective` to reduce the goal to its premises.

Rewrite using `[prodEquiv_finEmb]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, prodEquiv_unipGL_fst z hz1, mul_one, inv_mul_cancel]`. Express the relevant statement in the definitionally equal form `_ = (u : AdelicGLn.FiniteAdelicGL K n)`. Rewrite using `[hu, map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, prodEquiv_unipGL_snd]`.

Simplify using `only [c, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd ρ hρ, mul_one]`. Both sides reduce to the same expression.
-/
theorem exists_natCast_conj_mem (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) {ω Q : Set (AdelicGLn.AdelicGL K n)}
    (hω : IsCompact ω) (hQ : IsCompact Q) (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ k ∈ Q, ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
        (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
          (z p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a) →
        ∃ u : U, ((b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k)⁻¹ :
            AdelicGLn.AdelicGL K n) * unipGL z * (b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k) =
          finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := by
  classical
  set U' : Set (AdelicGLn.FiniteAdelicGL K n) :=
    Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))
  have hU' : IsOpen U' := (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have h1U' : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ U' := ⟨1, U.one_mem, rfl⟩
  set Cf : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => (AdelicGLn.prodEquiv K n (p.1 * p.2)).2) ''
      (ω ×ˢ Q)
  have hCf : IsCompact Cf := (hω.prod hQ).image
    (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp (continuous_fst.mul continuous_snd)))
  have hcont : Continuous fun q : (UPos n r → FiniteAdeleRing (𝓞 K) K) × AdelicGLn.FiniteAdelicGL K n =>
      q.2⁻¹ * unipGL q.1 * q.2 :=
    (continuous_snd.inv.mul (continuous_unipGL'.comp continuous_fst)).mul continuous_snd
  have hev : ∀ᶠ w in 𝓝 (0 : UPos n r → FiniteAdeleRing (𝓞 K) K), ∀ c ∈ Cf,
      c⁻¹ * unipGL w * c ∈ U' := by
    refine hCf.eventually_forall_of_forall_eventually fun c _ => ?_
    refine (hcont.tendsto ((0 : UPos n r → FiniteAdeleRing (𝓞 K) K), c)).eventually
      (hU'.mem_nhds ?_)
    simp only [unipGL_zero, mul_one, inv_mul_cancel]
    exact h1U'
  rw [nhds_pi] at hev
  have hev' : {w : UPos n r → FiniteAdeleRing (𝓞 K) K | ∀ c ∈ Cf, c⁻¹ * unipGL w * c ∈ U'} ∈
      Filter.pi fun _ => 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := hev
  rw [Filter.mem_pi] at hev'
  obtain ⟨I, -, tt, htt, hIt⟩ := hev'
  obtain ⟨M, hM, hMW⟩ := exists_natCast_mul_mem_of_mem_nhds K (Filter.iInter_mem.2 htt)
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  set w : UPos n r → FiniteAdeleRing (𝓞 K) K := fun p => (z p).2
  have hw : w ∈ I.pi tt := fun p _ => by
    obtain ⟨a, ha, hza⟩ := hz2 p
    have := hMW a ha
    rw [mem_iInter] at this
    change (z p).2 ∈ tt p
    rw [hza]
    exact this p
  set c := (AdelicGLn.prodEquiv K n (b * k)).2
  have hc : c ∈ Cf := ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  obtain ⟨u, huU, hu⟩ := hIt hw c hc
  refine ⟨⟨u, huU⟩, ?_⟩
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv,
      prodEquiv_unipGL_fst z hz1, mul_one, inv_mul_cancel]
  · change _ = (u : AdelicGLn.FiniteAdelicGL K n)
    rw [hu, map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv,
      prodEquiv_unipGL_snd]
    simp only [c, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd ρ hρ, mul_one]
    rfl

end PositivityTheory.Rg.Rs.diffstep

end
