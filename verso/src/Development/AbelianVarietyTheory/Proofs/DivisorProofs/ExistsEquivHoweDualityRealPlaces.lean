import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HoweRealKer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {om : Rep σ X W}

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hA`. Use `⟨inf_le_right, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ f hf f₁ hf₁`. Take `⟨D, hD, hDf⟩` from `h1 γ hγ`. Establish `e : f₁ = D f` using `(hDf f hf f₁).1 hf₁`.

Conclude with `Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hp.lie γ hγ f hf f₁ hf₁), e ▸ hD f hf⟩`. Introduce `k hk' f hf f₁ hf₁`. Take `⟨D, hD, hDf⟩` from `h2 k hk'`. Establish `e : f₁ = D f` using `(hDf f hf f₁).1 hf₁`. Establish `hP : f₁ ∈ M.Pol B.ψ B.emb` using `e ▸ hD f hf`.

Use `Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, sub_mem hP hf⟩` and prove the remaining obligations. Rewrite using `[map_sub, hp.cpt k hk' f hf f₁ hf₁, sub_self]`. Introduce `γ hγ f hf f₁ hf₁`. Take `⟨hf0, hfP⟩` from `Submodule.mem_inf.1 hf`. Take `⟨D, hD, hDf⟩` from `h3 γ hγ`.

Establish `e : f₁ = D f` using `(hDf f hfP f₁).1 hf₁`. Conclude with `Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.1 γ hγ f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩`. Introduce `k hk' f hf f₁ hf₁`. Take `⟨hf0, hfP⟩` from `Submodule.mem_inf.1 hf`. Take `⟨D, hD, hDf⟩` from `h4 k hk'`.

Establish `e : f₁ = D f` using `(hDf f hfP f₁).1 hf₁`. Conclude with `Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.2 k hk' f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩`.
-/
theorem thetaSub_ker (hA : GlobalTheory.RealActs.PolActs B M om) {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p) (hk : GlobalTheory.RealActs.KerStab B M om p) :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (LinearMap.ker p ⊓ M.Pol B.ψ B.emb) := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨D, hD, hDf⟩ := h1 γ hγ
    have e : f₁ = D f := (hDf f hf f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hp.lie γ hγ f hf f₁ hf₁), e ▸ hD f hf⟩
  · intro k hk' f hf f₁ hf₁
    obtain ⟨D, hD, hDf⟩ := h2 k hk'
    have e : f₁ = D f := (hDf f hf f₁).1 hf₁
    have hP : f₁ ∈ M.Pol B.ψ B.emb := e ▸ hD f hf
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, sub_mem hP hf⟩
    rw [map_sub, hp.cpt k hk' f hf f₁ hf₁, sub_self]
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨hf0, hfP⟩ := Submodule.mem_inf.1 hf
    obtain ⟨D, hD, hDf⟩ := h3 γ hγ
    have e : f₁ = D f := (hDf f hfP f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.1 γ hγ f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩
  · intro k hk' f hf f₁ hf₁
    obtain ⟨hf0, hfP⟩ := Submodule.mem_inf.1 hf
    obtain ⟨D, hD, hDf⟩ := h4 k hk'
    have e : f₁ = D f := (hDf f hfP f₁).1 hf₁
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hk.2 k hk' f hfP f₁ hf₁ (LinearMap.mem_ker.1 hf0)), e ▸ hD f hfP⟩

/- English proof (translation)
Take `⟨_, _, h3, h4⟩` from `hA`. Use `⟨sup_le hN.1 hN'.1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ f hf f₁ hf₁`. Conclude with `Submodule.mem_sup_left (hN.2.1 γ hγ f hf f₁ hf₁)`. Introduce `k hk f hf f₁ hf₁`.

Conclude with `Submodule.mem_sup_left (hN.2.2.1 k hk f hf f₁ hf₁)`. Introduce `γ hγ f hf f₁ hf₁`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hf`. Take `⟨D, hD, hDf⟩` from `h3 γ hγ`. Establish `hyP` using `hN.1 hy`.

Establish `hzP` using `hN'.1 hz`. Establish `e : f₁ = D (y + z)` using `(hDf _ (add_mem hyP hzP) f₁).1 hf₁`. Rewrite using `[e, map_add]`. Conclude with `add_mem (Submodule.mem_sup_left (hN.2.2.2.1 γ hγ y hy (D y) ((hDf y hyP (D y)).2 rfl))) (Submodule.mem_sup_right (hN'.2.2.2.1 γ hγ z hz (D z) ((hDf z hzP (D z)).2 rfl)))`. Introduce `k hk f hf f₁ hf₁`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hf`. Take `⟨D, hD, hDf⟩` from `h4 k hk`. Establish `hyP` using `hN.1 hy`. Establish `hzP` using `hN'.1 hz`. Establish `e : f₁ = D (y + z)` using `(hDf _ (add_mem hyP hzP) f₁).1 hf₁`.

Rewrite using `[e, map_add]`. Conclude with `add_mem (Submodule.mem_sup_left (hN.2.2.2.2 k hk y hy (D y) ((hDf y hyP (D y)).2 rfl))) (Submodule.mem_sup_right (hN'.2.2.2.2 k hk z hz (D z) ((hDf z hzP (D z)).2 rfl)))`.
-/
theorem thetaSub_sup (hA : GlobalTheory.RealActs.PolActs B M om) {N N' : Submodule ℂ (SInf F (Fin n × Fin d))}
    (hN : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N) (hN' : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N') :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (N ⊔ N') := by
  obtain ⟨_, _, h3, h4⟩ := hA
  refine ⟨sup_le hN.1 hN'.1, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hf₁
    exact Submodule.mem_sup_left (hN.2.1 γ hγ f hf f₁ hf₁)
  · intro k hk f hf f₁ hf₁
    exact Submodule.mem_sup_left (hN.2.2.1 k hk f hf f₁ hf₁)
  · intro γ hγ f hf f₁ hf₁
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨D, hD, hDf⟩ := h3 γ hγ
    have hyP := hN.1 hy
    have hzP := hN'.1 hz
    have e : f₁ = D (y + z) := (hDf _ (add_mem hyP hzP) f₁).1 hf₁
    rw [e, map_add]
    exact add_mem (Submodule.mem_sup_left (hN.2.2.2.1 γ hγ y hy (D y) ((hDf y hyP (D y)).2 rfl)))
      (Submodule.mem_sup_right (hN'.2.2.2.1 γ hγ z hz (D z) ((hDf z hzP (D z)).2 rfl)))
  · intro k hk f hf f₁ hf₁
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨D, hD, hDf⟩ := h4 k hk
    have hyP := hN.1 hy
    have hzP := hN'.1 hz
    have e : f₁ = D (y + z) := (hDf _ (add_mem hyP hzP) f₁).1 hf₁
    rw [e, map_add]
    exact add_mem (Submodule.mem_sup_left (hN.2.2.2.2 k hk y hy (D y) ((hDf y hyP (D y)).2 rfl)))
      (Submodule.mem_sup_right (hN'.2.2.2.2 k hk z hz (D z) ((hDf z hzP (D z)).2 rfl)))

/- English proof (translation)
Introduce `h`. Take `⟨x, hx⟩` from `exists_ne (0 : P)`. Establish `hx' : x ∈ (M.Pol B.ψ B.emb).map p` using `by rw [hp.onto]; exact Submodule.mem_top`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.1 hx'`. Rewrite `hf` using `[← h]`.

Conclude with `hx (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1)`.
-/
theorem ker_ne_pol {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hp : RealQuot B M om p) :
    LinearMap.ker p ⊓ M.Pol B.ψ B.emb ≠ M.Pol B.ψ B.emb := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  have hx' : x ∈ (M.Pol B.ψ B.emb).map p := by rw [hp.onto]; exact Submodule.mem_top
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx'
  rw [← h] at hf
  exact hx (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1)

/- English proof (translation)
Establish `key : ∀ f ∈ M.Pol B.ψ B.emb, p f ∈ N.map p → f ∈ N`. Introduce `f hf hpf`. Take `⟨y, hy, hyf⟩` from `Submodule.mem_map.1 hpf`. Establish `h0 : f - y ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb` using `Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hyf, sub_self]), sub_mem hf (hN.1 hy)⟩`. Use `add_mem (hle h0) hy` as an intermediate fact.

Simplify using `using this`. Break down `hi (N.map p) (fun γ hγ f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ f (key f hf hpf) f₁ hf₁)) (fun k hk f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.2 k hk f (key f hf hpf) f₁ hf₁)) with h | h` into its components or cases. Introduce `x hx`. Establish `: p x ∈ N.map p` using `Submodule.mem_map_of_mem hx`. Rewrite `this` using `[h]`.

Conclude with `Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this), hN.1 hx⟩`. Conclude with `absurd (le_antisymm hN.1 (fun f hf => key f hf (by rw [h]; exact Submodule.mem_top))) hne`.
-/
theorem le_ker_of_ge {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (hi : GlobalTheory.RealActs.Irred B M om p)
    {N : Submodule ℂ (SInf F (Fin n × Fin d))} (hN : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N)
    (hle : LinearMap.ker p ⊓ M.Pol B.ψ B.emb ≤ N) (hne : N ≠ M.Pol B.ψ B.emb) :
    N ≤ LinearMap.ker p ⊓ M.Pol B.ψ B.emb := by
  have key : ∀ f ∈ M.Pol B.ψ B.emb, p f ∈ N.map p → f ∈ N := by
    intro f hf hpf
    obtain ⟨y, hy, hyf⟩ := Submodule.mem_map.1 hpf
    have h0 : f - y ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hyf, sub_self]), sub_mem hf (hN.1 hy)⟩
    have := add_mem (hle h0) hy
    simpa using this
  rcases hi (N.map p)
      (fun γ hγ f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ f (key f hf hpf) f₁ hf₁))
      (fun k hk f hf f₁ hf₁ hpf => Submodule.mem_map_of_mem (hN.2.2.2.2 k hk f (key f hf hpf) f₁ hf₁)) with h | h
  · intro x hx
    have : p x ∈ N.map p := Submodule.mem_map_of_mem hx
    rw [h] at this
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this), hN.1 hx⟩
  · exact absurd (le_antisymm hN.1 (fun f hf => key f hf (by rw [h]; exact Submodule.mem_top))) hne

/- English proof (translation)
Establish `tp` using `thetaSub_ker hA hp hkp`. Establish `tq` using `thetaSub_ker hA hq hkq`. Establish `hS` using `thetaSub_sup hA tp tq`. Establish `hne` using `hH _ _ tp tq (ker_ne_pol hp) (ker_ne_pol hq)`. Establish `h1` using `le_ker_of_ge hip hS le_sup_left hne`.

Establish `h2` using `le_ker_of_ge hiq hS le_sup_right hne`. Conclude with `le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)`.
-/
theorem ker_eq {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [Nontrivial P] [Nontrivial Q]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} {q : SInf F (Fin n × Fin d) →ₗ[ℂ] Q}
    (hA : GlobalTheory.RealActs.PolActs B M om)
    (hH : ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' →
      N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb)
    (hp : RealQuot B M om p) (hq : RealQuot B M om q) (hkp : GlobalTheory.RealActs.KerStab B M om p)
    (hkq : GlobalTheory.RealActs.KerStab B M om q) (hip : GlobalTheory.RealActs.Irred B M om p) (hiq : GlobalTheory.RealActs.Irred B M om q) :
    LinearMap.ker p ⊓ M.Pol B.ψ B.emb = LinearMap.ker q ⊓ M.Pol B.ψ B.emb := by
  have tp := thetaSub_ker hA hp hkp
  have tq := thetaSub_ker hA hq hkq
  have hS := thetaSub_sup hA tp tq
  have hne := hH _ _ tp tq (ker_ne_pol hp) (ker_ne_pol hq)
  have h1 := le_ker_of_ge hip hS le_sup_left hne
  have h2 := le_ker_of_ge hiq hS le_sup_right hne
  exact le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M om P Q _ _ _ _ p q hA hH hp hq hPn hQn hkp hkq hip hiq`. Establish `hK` using `ker_eq hA hH hp hq hkp hkq hip hiq`. Use `set Pol := M.Pol B.ψ B.emb`. Set `p'` to `p.domRestrict Pol`. Set `q'` to `q.domRestrict Pol`.

Establish `sp : Function.Surjective p'`. Introduce `y`. Establish `hy : y ∈ Pol.map p` using `by rw [hp.onto]; exact Submodule.mem_top`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.1 hy`. Conclude with `⟨⟨f, hf⟩, rfl⟩`.

Establish `sq : Function.Surjective q'`. Introduce `y`. Establish `hy : y ∈ Pol.map q` using `by rw [hq.onto]; exact Submodule.mem_top`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.1 hy`. Conclude with `⟨⟨f, hf⟩, rfl⟩`.

Establish `hker : LinearMap.ker p' = LinearMap.ker q'`. Use extensionality with `⟨f, hf⟩`. Simplify using `only [p', q', LinearMap.mem_ker, LinearMap.domRestrict_apply]`. Use `SetLike.ext_iff.1 hK f` as an intermediate fact. Simplify using `only [Submodule.mem_inf, LinearMap.mem_ker] at this`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(this.1 ⟨h, hf⟩).1`. Introduce `h`. Conclude with `(this.2 ⟨h, hf⟩).1`.

Use `⟨(p'.quotKerEquivOfSurjective sp).symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans (q'.quotKerEquivOfSurjective sq)), fun f hf => ?_⟩` and prove the remaining obligations. Establish `e1 : (p'.quotKerEquivOfSurjective sp).symm (p f) = Submodule.Quotient.mk ⟨f, hf⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [LinearEquiv.trans_apply, e1, Submodule.quotEquivOfEq_mk]`.

Both sides reduce to the same expression.
-/
theorem exists_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (om : Rep σ X W) (P Q : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (q : SInf F (Fin n × Fin d) →ₗ[ℂ] Q),
    GlobalTheory.RealActs.PolActs B M om →
    (∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' → N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb) →
    RealQuot B M om p → RealQuot B M om q → Nontrivial P → Nontrivial Q → GlobalTheory.RealActs.KerStab B M om p → GlobalTheory.RealActs.KerStab B M om q →
    GlobalTheory.RealActs.Irred B M om p → GlobalTheory.RealActs.Irred B M om q → ∃ ψ : P ≃ₗ[ℂ] Q, ∀ f ∈ M.Pol B.ψ B.emb, q f = ψ (p f) := by
  intro F E _ _ _ _ _ σ B n d X W M om P Q _ _ _ _ p q hA hH hp hq hPn hQn hkp hkq hip hiq
  have hK := ker_eq hA hH hp hq hkp hkq hip hiq
  set Pol := M.Pol B.ψ B.emb
  let p' := p.domRestrict Pol
  let q' := q.domRestrict Pol
  have sp : Function.Surjective p' := by
    intro y
    have hy : y ∈ Pol.map p := by rw [hp.onto]; exact Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨f, hf⟩, rfl⟩
  have sq : Function.Surjective q' := by
    intro y
    have hy : y ∈ Pol.map q := by rw [hq.onto]; exact Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨f, hf⟩, rfl⟩
  have hker : LinearMap.ker p' = LinearMap.ker q' := by
    ext ⟨f, hf⟩
    simp only [p', q', LinearMap.mem_ker, LinearMap.domRestrict_apply]
    have := SetLike.ext_iff.1 hK f
    simp only [Submodule.mem_inf, LinearMap.mem_ker] at this
    constructor
    · intro h; exact (this.1 ⟨h, hf⟩).1
    · intro h; exact (this.2 ⟨h, hf⟩).1
  refine ⟨(p'.quotKerEquivOfSurjective sp).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (q'.quotKerEquivOfSurjective sq)), fun f hf => ?_⟩
  have e1 : (p'.quotKerEquivOfSurjective sp).symm (p f) = Submodule.Quotient.mk ⟨f, hf⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearEquiv.trans_apply, e1, Submodule.quotEquivOfEq_mk]
  rfl

end GlobalTheory.HoweRealKer

end
