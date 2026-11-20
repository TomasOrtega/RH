import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

/- English proof (translation)
Take `⟨h1, h2⟩` from `GlobalTheory.TopStep.liftFr_spec hd w`. Use `set fr := d.liftFr w with hfr`. Establish `e : fr (fr.symm x) = x` using `fr.apply_symm_apply x`. Establish `hs : fr.symm x ∈ stdAt E n w.1` using `(h1 _).1 (by rwa [e])`. Establish `hr` using `h2 _ hs`.

Rewrite `hr` using `[e, h0]`. Establish `hi` using `GlobalTheory.TopStep.mem_stdAt.1 hs`. Establish `hs' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • fr.symm x ∈ stdAt E n w.1` using `GlobalTheory.TopStep.mem_stdAt.2 fun i => by`. Use `GlobalTheory.TopStep.intAt_div_of_redP hq (hi i) (congrFun hr i).symm` as an intermediate fact. Rewrite `this` using `[div_eq_inv_mul]`. Then use the resulting hypothesis.

Use `(h1 _).2 hs'` as an intermediate fact. Rewrite `this` using `[map_smul, e]`. Then use the resulting hypothesis.
-/
theorem inv_smul_mem_of_be_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.at w.1) (h0 : d.be w x = 0) :
    ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • x ∈ d.at w.1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TopStep.liftFr_spec hd w
  set fr := d.liftFr w with hfr
  have e : fr (fr.symm x) = x := fr.apply_symm_apply x
  have hs : fr.symm x ∈ stdAt E n w.1 := (h1 _).1 (by rwa [e])
  have hr := h2 _ hs
  rw [e, h0] at hr
  have hi := GlobalTheory.TopStep.mem_stdAt.1 hs
  have hs' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E)⁻¹ • fr.symm x ∈ stdAt E n w.1 := GlobalTheory.TopStep.mem_stdAt.2 fun i => by
    have := GlobalTheory.TopStep.intAt_div_of_redP hq (hi i) (congrFun hr i).symm
    rwa [div_eq_inv_mul] at this
  have := (h1 _).2 hs'
  rwa [map_smul, e] at this

/- English proof (translation)
Establish `hq0 : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) ≠ 0` using `GlobalTheory.TopStep.qOf_ne_zero`. Establish `hqz : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y') ∈ d.at w.1` using `GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) hz`. Establish `e1 : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y')) = 0`. Rewrite using `[GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) hz, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul]`. Establish `e2` using `hd.be_add w _ hqz _ hy'`.

Rewrite `e2` using `[← smul_add, sub_add_cancel, e1, zero_add, ← e]`. Establish `hx : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (y - y') ∈ d.at w.1`. Rewrite using `[smul_sub]`. Conclude with `sub_mem hy hy'`. Establish `e3` using `hd.be_add w _ hx _ hy'`.

Rewrite `e3` using `[← smul_add, sub_add_cancel, e2, right_eq_add]`. Use `inv_smul_mem_of_be_eq_zero hd w hq hx e3` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hq0, one_smul]`. Then use the resulting hypothesis.
-/
theorem sub_mem_of_be_eq {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) (w : SG)
    (hq : ((Formalism.L2.Col.qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2) {y y' z : Sp E n}
    (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.at w.1) (hy' : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y' ∈ d.at w.1)
    (hz : z - y' ∈ d.at w.1)
    (e : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)) :
    y - y' ∈ d.at w.1 := by
  have hq0 : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hqz : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y') ∈ d.at w.1 :=
    GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) hz
  have e1 : d.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y')) = 0 := by
    rw [GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) hz, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul]
  have e2 := hd.be_add w _ hqz _ hy'
  rw [← smul_add, sub_add_cancel, e1, zero_add, ← e] at e2
  have hx : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (y - y') ∈ d.at w.1 := by
    rw [smul_sub]
    exact sub_mem hy hy'
  have e3 := hd.be_add w _ hx _ hy'
  rw [← smul_add, sub_add_cancel, e2, right_eq_add] at e3
  have := inv_smul_mem_of_be_eq_zero hd w hq hx e3
  rwa [smul_smul, inv_mul_cancel₀ hq0, one_smul] at this

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_coset {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] {L : Submodule A M} {y z : M} :
    z ∈ {z | z - y ∈ L} ↔ z - y ∈ L := Iff.rfl

/- English proof (translation)
Use `Set.ext fun z => ?_` and prove the remaining obligations. Rewrite using `[mem_coset, mem_coset]`. Use `⟨fun h' => ?_, fun h' => ?_⟩` and prove the remaining obligations. Use `add_mem h' h` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.

Use `sub_mem h' h` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.
-/
theorem coset_eq {M : Type} [AddCommGroup M] {A : Type} [Ring A] [Module A M] (L : Submodule A M) {y y' : M} (h : y - y' ∈ L) :
    {z | z - y ∈ L} = {z | z - y' ∈ L} := by
  refine Set.ext fun z => ?_
  rw [mem_coset, mem_coset]
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  · have := add_mem h' h
    rwa [sub_add_sub_cancel] at this
  · have := sub_mem h' h
    rwa [sub_sub_sub_cancel_right] at this

/- English proof (translation)
Introduce `X Pr R sel S mu cst u j hQ hq q q' hd hb`. Establish `hP : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs` using `fun P => by`. Use `P.2` as an intermediate fact. Simplify `this` using `[rowSG, uSG, hQ]`. Establish `hfr : q.1.1 = q'.1.1`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hE : ∀ a, a ∈ QE sel (mu : Chr X.F X.E X.K) → False` using `fun a ha => by`. Rewrite `ha` using `[hQ]`. Simplify using `at ha`. Conclude with `Prod.ext hd (funext fun P => (hE _ P.2).elim)`.

It suffices to establish `h2 : q.1.2 = q'.1.2 from Subtype.ext (Prod.ext hfr h2)`. Distinguish the cases in `hj : j + 1 = R.m`. Take `⟨y, hy, eY⟩` from `q.mem_ybSet hj`. Take `⟨y', hy', eY'⟩` from `q'.mem_ybSet hj`. Establish `eN : q'.1.1.deco.1.N = q.1.1.deco.1.N` using `by rw [hd]`.

Rewrite `hy'`, `eY'` using `[eN]`. Establish `key : ∀ e : rowSG Pr sel mu → ℤ, (∀ P, e P = 0) → y - y' ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N e`. Introduce `e he`. Use `(mem_locLat _ _ _ _).2 fun P => ?_` and prove the remaining obligations. Rewrite using `[he P, zpow_zero, inv_one, one_smul]`.

Establish `hm : q.1.1.deco.1.be ⟨P.1, hP P⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar q ⟨P.1, hP P⟩` using `⟨y, by rw [eY, mem_coset, sub_self]; exact zero_mem _, rfl⟩`. Rewrite `hm` using `[congrFun hb ⟨P.1, hP P⟩]`. Take `⟨z, hz, ez⟩` from `hm`. Rewrite `ez` using `[← hd]`. Rewrite `hz` using `[eY']`.

Establish `hz'` using `(mem_locLat _ _ _ _).1 (mem_coset.1 hz) P`. Rewrite `hz'` using `[if_pos (hP P), zpow_zero, inv_one, one_smul]`. Establish `h1` using `(mem_locLat _ _ _ _).1 hy P`. Establish `h2` using `(mem_locLat _ _ _ _).1 hy' P`. Rewrite `h1`, `h2` using `[if_pos (hP P), _root_.zpow_neg_one, inv_inv]`.

Conclude with `sub_mem_of_be_eq q.1.1.deco.2 ⟨P.1, hP P⟩ (hq _ (hP P)) h1 h2 hz' ez`. Rewrite using `[eY, eY']`. Conclude with `coset_eq _ (key _ fun P => if_pos (hP P))`. Establish `h1` using `q.2`. Establish `h1'` using `q'.2`.

Rewrite `h1`, `h1'` using `[ysAt_ys_of_ne sel mu cst hj]`. Conclude with `h1.trans h1'.symm`.
-/
theorem eq_of_deco_bar : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ q q' : PtAt R sel mu cst u j, q.1.1.deco = q'.1.1.deco → MemChart.bar q = MemChart.bar q' → q = q' := by
  intro X Pr R sel S mu cst u j hQ hq q q' hd hb
  have hP : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P => by
    have := P.2
    simpa [rowSG, uSG, hQ] using this
  have hfr : q.1.1 = q'.1.1 := by
    apply Subtype.ext
    have hE : ∀ a, a ∈ QE sel (mu : Chr X.F X.E X.K) → False := fun a ha => by
      rw [hQ] at ha
      simp at ha
    exact Prod.ext hd (funext fun P => (hE _ P.2).elim)
  suffices h2 : q.1.2 = q'.1.2 from Subtype.ext (Prod.ext hfr h2)
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := q.mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := q'.mem_ybSet hj
    have eN : q'.1.1.deco.1.N = q.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have key : ∀ e : rowSG Pr sel mu → ℤ, (∀ P, e P = 0) → y - y' ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N e := by
      intro e he
      refine (mem_locLat _ _ _ _).2 fun P => ?_
      rw [he P, zpow_zero, inv_one, one_smul]
      have hm : q.1.1.deco.1.be ⟨P.1, hP P⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar q ⟨P.1, hP P⟩ :=
        ⟨y, by rw [eY, mem_coset, sub_self]; exact zero_mem _, rfl⟩
      rw [congrFun hb ⟨P.1, hP P⟩] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos (hP P), zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos (hP P), _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq q.1.1.deco.2 ⟨P.1, hP P⟩ (hq _ (hP P)) h1 h2 hz' ez
    rw [eY, eY']
    exact coset_eq _ (key _ fun P => if_pos (hP P))
  · have h1 := q.2
    have h1' := q'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.MemChart
