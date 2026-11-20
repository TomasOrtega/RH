import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntegralExpRename

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser')

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Param

variable (p : ℕ) [hp : Fact p.Prime]

def tOf {K' σ τ : Type} [Field K'] (vp : K') (μ : PowerSeries K') (L : σ → MvPowerSeries τ K') :
    σ → MvPowerSeries τ K' :=
  fun i => PowerSeries.subst (L i) (PowerSeries.C vp * μ)

/- English proof (translation)
Use `first`. Consider the case `(rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; unfold logF; simp)`. Consider the case `(unfold logF; simp)`. Consider the case `(simp [logF, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])`.
-/
private theorem constantCoeff_logF_eq_zero : PowerSeries.constantCoeff (logF p) = 0 := by
  first
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; unfold logF; simp)
  | (unfold logF; simp)
  | (simp [logF, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst a` using `by first`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero ha`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [ha]; exact IsNilpotent.zero)`. Take `⟨g, rfl⟩` from `PowerSeries.X_dvd_iff.mpr hf`. Use `first`.

Consider the case `rw [PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]`. Consider the case `rw [← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]`.
-/
private theorem cc_subst_lemma_2 {τ S : Type} [CommRing S] {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries S} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [ha]; exact IsNilpotent.zero)
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  first
  | rw [PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]
  | rw [← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs,
      map_mul, ha, zero_mul]

/- English proof (translation)
Use `cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) ?_` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_logF_eq_zero, map_zero]`.
-/
theorem th_lX_const (K1 : Type) [Field K1] [Algebra (K0 p) K1] {σ : Type} (i : σ) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
  refine cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_logF_eq_zero, map_zero]

/- English proof (translation)
Unfold `inParam inParamK`. Use `congr 1`.
-/
theorem th_inParam_eq {σ : Type} (f : MvPowerSeries σ (K0 p)) : inParam p f = inParamK p (K0 p) f := by
  unfold inParam inParamK
  congr 1

/- English proof (translation)
Unfold `inParamK`. Rewrite using `[MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (th_lX_const p K1))]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ K1)` using `PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`.

Rewrite using `[PowerSeries.map_subst hX, MvPowerSeries.map_X, map_logF, map_logF]`. Use `congr 1`. Use extensionality with `n`. Unfold `lgF`. Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[apply_ite (algebraMap K1 K'), map_zero, map_inv₀, map_pow, map_natCast]`.
-/
theorem th_inParamK_map {σ : Type} [Finite σ] (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K']
    [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (U : MvPowerSeries σ K1) :
    inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U) =
      MvPowerSeries.map (algebraMap K1 K') (inParamK p K1 U) := by
  unfold inParamK
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (th_lX_const p K1))]
  congr 1
  funext i
  have hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ K1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.map_subst hX, MvPowerSeries.map_X, map_logF, map_logF]
  congr 1
  ext n
  unfold lgF
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [apply_ite (algebraMap K1 K'), map_zero, map_inv₀, map_pow, map_natCast]

/- English proof (translation)
Unfold `tOf`. Use `cc_subst_lemma_2 (hL0 i) ?_` and prove the remaining obligations. Rewrite using `[map_mul, h0, mul_zero]`.
-/
theorem th_tOf_const {K' σ τ : Type} [Field K'] (vp : K') (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (i : σ) :
    MvPowerSeries.constantCoeff (tOf vp μ L i) = 0 := by
  unfold tOf
  refine cc_subst_lemma_2 (hL0 i) ?_
  rw [map_mul, h0, mul_zero]

/- English proof (translation)
Establish `hsh : MvPowerSeries.HasSubst (tOf vp μ L)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (th_tOf_const vp μ h0 L hL0)`. Unfold `inParamK`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (th_lX_const p K')) hsh]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Establish `hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ K')` using `PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Establish `e3 : MvPowerSeries.subst (tOf vp μ L) (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K') (PowerSeries.map (algebraMap (K0 p) K') (logF p))) = PowerSeries.subst (MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.X i : MvPowerSeries σ K')) (PowerSeries.map (algebraMap (K0 p) …` using `MvPowerSeries.subst_comp_subst_apply (PowerSeries.hasSubst_iff.1 hX) hsh _`. Rewrite using `[e3, MvPowerSeries.subst_X hsh, map_logF]`. Conclude with `(log_at p K' vp μ h0 h1 (L i) (hL0 i)).symm`.
-/
theorem th_subst_log (K' : Type) [Field K'] [Algebra (K0 p) K'] {σ τ : Type} [Finite σ] (vp : K')
    (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (U : MvPowerSeries σ K') :
    MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U =
      MvPowerSeries.subst (tOf vp μ L) (inParamK p K' U) := by
  have hsh : MvPowerSeries.HasSubst (tOf vp μ L) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (th_tOf_const vp μ h0 L hL0)
  unfold inParamK
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (th_lX_const p K')) hsh]
  congr 1
  funext i
  have hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ K') :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have e3 : MvPowerSeries.subst (tOf vp μ L) (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K')
      (PowerSeries.map (algebraMap (K0 p) K') (logF p))) =
      PowerSeries.subst (MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.X i : MvPowerSeries σ K'))
        (PowerSeries.map (algebraMap (K0 p) K') (logF p)) :=
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.hasSubst_iff.1 hX) hsh _
  rw [e3, MvPowerSeries.subst_X hsh, map_logF]
  exact (log_at p K' vp μ h0 h1 (L i) (hL0 i)).symm

/- English proof (translation)
Use `first`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero h`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h s]; exact IsNilpotent.zero)`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h s]; exact IsNilpotent.zero)`.

Consider the case `exact ⟨fun s => by rw [h s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩`.
-/
private theorem hasSubst_of_constantCoeff_eq_zero' {κ τ S : Type} [CommRing S] [Finite κ] {a : κ → MvPowerSeries τ S}
    (h : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h s]; exact IsNilpotent.zero)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h s]; exact IsNilpotent.zero)
  | exact ⟨fun s => by rw [h s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩

/- English proof (translation)
Use `hasSubst_of_constantCoeff_eq_zero' fun i => ?_` and prove the remaining obligations. Conclude with `cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) (constantCoeff_logF_eq_zero p)`.
-/
theorem th_hasSubst_lX {σ : Type} [Finite σ] : MvPowerSeries.HasSubst
    (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) := by
  refine hasSubst_of_constantCoeff_eq_zero' fun i => ?_
  exact cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) (constantCoeff_logF_eq_zero p)

/- English proof (translation)
Establish `key : ∀ d : κ →₀ ℕ, MvPowerSeries.coeff d f • MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0`. Introduce `d`. Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Rewrite `hf` using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`.

Rewrite using `[hf, zero_smul]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, d s ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hd (Finsupp.ext hcon)`.

Establish `h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0`. Rewrite using `[Finsupp.prod, map_prod]`. Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, h s, zero_pow hs])`. Rewrite using `[h0, smul_zero]`. Rewrite using `[MvPowerSeries.constantCoeff_subst (hasSubst_of_constantCoeff_eq_zero' h)]`.

Simplify using `only [key, finsum_zero]`.
-/
private theorem constantCoeff_subst_eq_zero' {κ τ S : Type} [CommRing S] [Finite κ] {a : κ → MvPowerSeries τ S}
    (h : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {f : MvPowerSeries κ S}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  have key : ∀ d : κ →₀ ℕ,
      MvPowerSeries.coeff d f • MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
      rw [hf, zero_smul]
    · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hd (Finsupp.ext hcon)
      have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
        rw [Finsupp.prod, map_prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, h s, zero_pow hs])
      rw [h0, smul_zero]
  rw [MvPowerSeries.constantCoeff_subst (hasSubst_of_constantCoeff_eq_zero' h)]
  simp only [key, finsum_zero]

/- English proof (translation)
Unfold `inParam`. Conclude with `constantCoeff_subst_eq_zero' (fun i => cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) (constantCoeff_logF_eq_zero p)) hf`.
-/
theorem th_inParam_const {σ : Type} [Finite σ] {f : MvPowerSeries σ (K0 p)}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (inParam p f) = 0 := by
  unfold inParam
  exact constantCoeff_subst_eq_zero' (fun i => cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) (constantCoeff_logF_eq_zero p)) hf

/- English proof (translation)
Establish `ha` using `th_hasSubst_lX p (σ := σ)`. Unfold `inParam`. Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_sub]`.
-/
theorem th_inParam_sub {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f - g) = inParam p f - inParam p g := by
  have ha := th_hasSubst_lX p (σ := σ)
  unfold inParam
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sub]

/- English proof (translation)
Establish `ha` using `th_hasSubst_lX p (σ := σ)`. Unfold `inParam`. Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_neg]`.
-/
theorem th_inParam_neg {σ : Type} [Finite σ] (f : MvPowerSeries σ (K0 p)) :
    inParam p (-f) = -inParam p f := by
  have ha := th_hasSubst_lX p (σ := σ)
  unfold inParam
  rw [← MvPowerSeries.coe_substAlgHom ha, map_neg]

/- English proof (translation)
Establish `ha` using `th_hasSubst_lX p (σ := σ)`. Unfold `inParam`. Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_sum]`.
-/
theorem th_inParam_sum {σ α : Type} [Finite σ] (s : Finset α) (f : α → MvPowerSeries σ (K0 p)) :
    inParam p (∑ a ∈ s, f a) = ∑ a ∈ s, inParam p (f a) := by
  have ha := th_hasSubst_lX p (σ := σ)
  unfold inParam
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_eq_zero' fun k => MvPowerSeries.constantCoeff_X (φ k)`.
-/
theorem th_ren_hasSubst {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ) :
    MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) :=
  hasSubst_of_constantCoeff_eq_zero' fun k => MvPowerSeries.constantCoeff_X (φ k)

/- English proof (translation)
Establish `ha` using `th_ren_hasSubst (R := R) φ`. Unfold `ren`. Rewrite using `[← MvPowerSeries.coe_substAlgHom ha, map_sub]`.
-/
theorem th_ren_sub {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ) (f g : MvPowerSeries κ R) :
    ren φ (f - g) = ren φ f - ren φ g := by
  have ha := th_ren_hasSubst (R := R) φ
  unfold ren
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sub]

/- English proof (translation)
Unfold `ren`. Conclude with `constantCoeff_subst_eq_zero' (fun k => MvPowerSeries.constantCoeff_X (φ k)) hf`.
-/
theorem th_ren_const {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ) {f : MvPowerSeries κ R}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ren φ f) = 0 := by
  unfold ren
  exact constantCoeff_subst_eq_zero' (fun k => MvPowerSeries.constantCoeff_X (φ k)) hf

/- English proof (translation)
Unfold `inParam ren`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (th_ren_hasSubst φ) (th_hasSubst_lX p), MvPowerSeries.subst_comp_subst_apply (th_hasSubst_lX p) (th_ren_hasSubst φ)]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[MvPowerSeries.subst_X (th_hasSubst_lX p)]`.

Establish `hX : PowerSeries.HasSubst (MvPowerSeries.X k : MvPowerSeries κ (K0 p))` using `PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X k)`. Establish `e3 : MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ (K0 p)) (logF p)) = PowerSeries.subst (MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) (MvPowerSeries.X k : …` using `MvPowerSeries.subst_comp_subst_apply (PowerSeries.hasSubst_iff.1 hX) (th_ren_hasSubst φ) _`. Rewrite using `[e3, MvPowerSeries.subst_X (th_ren_hasSubst φ)]`.
-/
theorem th_inParam_ren {κ σ : Type} [Finite κ] [Finite σ] (φ : κ → σ) (f : MvPowerSeries κ (K0 p)) :
    inParam p (ren φ f) = ren φ (inParam p f) := by
  unfold inParam ren
  rw [MvPowerSeries.subst_comp_subst_apply (th_ren_hasSubst φ) (th_hasSubst_lX p),
    MvPowerSeries.subst_comp_subst_apply (th_hasSubst_lX p) (th_ren_hasSubst φ)]
  congr 1
  funext k
  rw [MvPowerSeries.subst_X (th_hasSubst_lX p)]
  have hX : PowerSeries.HasSubst (MvPowerSeries.X k : MvPowerSeries κ (K0 p)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X k)
  have e3 : MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)))
      (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ (K0 p)) (logF p)) =
      PowerSeries.subst (MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)))
        (MvPowerSeries.X k : MvPowerSeries κ (K0 p))) (logF p) :=
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.hasSubst_iff.1 hX) (th_ren_hasSubst φ) _
  rw [e3, MvPowerSeries.subst_X (th_ren_hasSubst φ)]

/- English proof (translation)
Unfold `sub2 ren`. Use `congr 1`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `fin_cases k <;> rfl`.
-/
theorem substitution_of_variables {σ : Type} (be : MvPowerSeries (Fin 2) (K0 p)) (a b : σ) :
    sub2 p be (MvPowerSeries.X a) (MvPowerSeries.X b) = ren ![a, b] be := by
  unfold sub2 ren
  congr 1
  funext k
  fin_cases k <;> rfl

def Gt (E : Type) [Fintype E] (c c' : K0 p) : MvPowerSeries (E ⊕ E) (K0 p) :=
  ∑ e : E, ren ![Sum.inl e, Sum.inr e] (Gser p c c')

/- English proof (translation)
Establish `hcz` using `charZero_K' p (K0 p)`. Take `⟨hc0, h, hh0, hE⟩` from `hPh`. Establish `hPsi0 : MvPowerSeries.constantCoeff (∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) : MvPowerSeries (E ⊕ E) (K0 p)) = 0`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ hbe0`.

Establish `hPh0 : MvPowerSeries.constantCoeff Ph = 0`. Rewrite `hc0` using `[map_sub, hPsi0, sub_zero]`. Conclude with `hc0`. Establish `hGt0 : MvPowerSeries.constantCoeff (Gt p E c c') = 0`. Unfold `Gt`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun e _ => th_ren_const _ hG0`. Establish `hδ : E0 p (inParam p Ph - Gt p E c c')`. Establish `e : inParam p Ph - Gt p E c c' = inParam p (Ph - ∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) + ∑ e : E, ren ![Sum.inl e, Sum.inr e] (inParam p be - Gser p c c')`. Rewrite using `[th_inParam_sub, th_inParam_sum]`.

Simplify using `only [substitution_of_variables, th_inParam_ren, th_ren_sub, Finset.sum_sub_distrib, Gt]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `integralExp_add p ⟨th_inParam_const p hc0, h, hh0, hE⟩ (integralExp_sum p _ _ fun e _ => integralExp_rename p _ (hβ e))`. Take `⟨w, hw⟩` from `exp_neg_integral p hδ`.

Establish `ht0` using `th_tOf_const vp μ h0 L hL0`. Establish `htI : ∀ i, IntR (Rp p K' vp) (tOf vp μ L i)` using `fun i => IntR_psubst (hL0 i) (hL i) fun n => by`. Rewrite using `[PowerSeries.coeff_C_mul]`. Conclude with `(Rp p K' vp).mul_mem (vp_mem_Rp p K' vp) (hμ n)`. Use `⟨MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.map (algebraMap (K0 p) K') (MvPowerSeries.map (algebraMap (WW p) (K0 p)) w)), IntR_subst _ ht0 htI fun n => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]`. Conclude with `W_mem_Rp p K' vp _`. Establish `e1 : inParam p (expS p (-Ph)) = expK (-(Gt p E c c')) * expK (-(inParam p Ph - Gt p E c c'))`. Establish `: inParam p (expS p (-Ph)) = expK (inParam p (-Ph))`. Unfold `inParam`.

Conclude with `th_subst_expK _ (fun i => by`. Use `th_lX_const p (K0 p) i` as an intermediate fact. Rewrite using `[Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hPh0, neg_zero])` and apply the resulting hypothesis. Rewrite using `[this, ← expK_add (by rw [map_neg, hGt0, neg_zero]) (by rw [map_neg, hδ.1, neg_zero]), th_inParam_neg]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[th_subst_log p K' vp μ h0 h1 L hL0, th_inParamK_map p (K0 p) K', ← th_inParam_eq, e1, hw, map_mul, th_map_expK, map_neg, MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero ht0)]`.
-/
theorem th_reduce {E τ : Type} [Fintype E] (be : MvPowerSeries (Fin 2) (K0 p))
    (hbe0 : MvPowerSeries.constantCoeff be = 0) (c c' : K0 p)
    (hG0 : MvPowerSeries.constantCoeff (Gser p c c') = 0) (hβ : E → E0 p (inParam p be - Gser p c c'))
    (Ph : MvPowerSeries (E ⊕ E) (K0 p))
    (hPh : Simeq p Ph (∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))))
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (μ : PowerSeries K')
    (h0 : PowerSeries.constantCoeff μ = 0) (hμ : ∀ n, PowerSeries.coeff n μ ∈ Rp p K' vp)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : E ⊕ E → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0)
    (hL : ∀ i, IntR (Rp p K' vp) (L i)) :
    ∃ V' : MvPowerSeries τ K', IntR (Rp p K' vp) V' ∧
      MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i)
          (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        MvPowerSeries.subst (tOf vp μ L) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K') (Gt p E c c')))) * V' := by
  have hcz := charZero_K' p (K0 p)
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hPsi0 : MvPowerSeries.constantCoeff
      (∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
        MvPowerSeries (E ⊕ E) (K0 p)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ hbe0
  have hPh0 : MvPowerSeries.constantCoeff Ph = 0 := by
    rw [map_sub, hPsi0, sub_zero] at hc0
    exact hc0
  have hGt0 : MvPowerSeries.constantCoeff (Gt p E c c') = 0 := by
    unfold Gt
    rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => th_ren_const _ hG0
  have hδ : E0 p (inParam p Ph - Gt p E c c') := by
    have e : inParam p Ph - Gt p E c c' =
        inParam p (Ph - ∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) +
          ∑ e : E, ren ![Sum.inl e, Sum.inr e] (inParam p be - Gser p c c') := by
      rw [th_inParam_sub, th_inParam_sum]
      simp only [substitution_of_variables, th_inParam_ren, th_ren_sub, Finset.sum_sub_distrib, Gt]
      ring
    rw [e]
    exact integralExp_add p ⟨th_inParam_const p hc0, h, hh0, hE⟩ (integralExp_sum p _ _ fun e _ => integralExp_rename p _ (hβ e))
  obtain ⟨w, hw⟩ := exp_neg_integral p hδ
  have ht0 := th_tOf_const vp μ h0 L hL0
  have htI : ∀ i, IntR (Rp p K' vp) (tOf vp μ L i) := fun i => IntR_psubst (hL0 i) (hL i) fun n => by
    rw [PowerSeries.coeff_C_mul]
    exact (Rp p K' vp).mul_mem (vp_mem_Rp p K' vp) (hμ n)
  refine ⟨MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.map (algebraMap (K0 p) K')
    (MvPowerSeries.map (algebraMap (WW p) (K0 p)) w)), IntR_subst _ ht0 htI fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    exact W_mem_Rp p K' vp _
  · have e1 : inParam p (expS p (-Ph)) = expK (-(Gt p E c c')) * expK (-(inParam p Ph - Gt p E c c')) := by
      have : inParam p (expS p (-Ph)) = expK (inParam p (-Ph)) := by
        unfold inParam
        exact th_subst_expK _ (fun i => by
          have := th_lX_const p (K0 p) i
          rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hPh0, neg_zero])
      rw [this, ← expK_add (by rw [map_neg, hGt0, neg_zero]) (by rw [map_neg, hδ.1, neg_zero]), th_inParam_neg]
      congr 1
      ring
    rw [th_subst_log p K' vp μ h0 h1 L hL0, th_inParamK_map p (K0 p) K', ← th_inParam_eq, e1, hw, map_mul,
      th_map_expK, map_neg, MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero ht0)]

end Param

end Formalism.MainNotions.FormalGroupSystem.Pf
