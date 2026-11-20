import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsDef
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0 RowTiePProj

namespace GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

/- English proof (translation)
Establish `hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0` using `const_of_lim Y hT`. Establish `act0 : ∀ x i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0` using `Y.B.A.const`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Use function extensionality and compare the values at `i`.

Establish `L` using `TendsS.comp1 (φ := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a) (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i`. Establish `R` using `TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (fun n => act0 _) hφ0 (fun _ => TendsS.const _) hT i`. Establish `eq : (fun n => comp1 (Y.B.A.act (M n * ε ^ V.l ^ n)) (Y.B.A.act a) i) = fun n => comp1 (Y.B.A.act a) (Y.B.A.act (M n * ε ^ V.l ^ n)) i` using `funext fun n => by`. Rewrite using `[← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]`. Rewrite `L` using `[eq]`.

Conclude with `L.unique R`. Take `⟨E, -, -, -, hET⟩` from `StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx (fun _ => 1) (fun N a => by rw [sub_self, map_zero]; exact VF.Ge.zero _)`. Establish `hElim : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (MvPowerSeries.coeff μ (E i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))`. Introduce `N i μ`. Take `⟨n0, h⟩` from `hET i μ N`.

Conclude with `⟨n0, fun n hn => by simpa only [one_mul] using h n hn⟩`. Establish `hEspan` using `hLie C V O dd Y d I0 p ε hε hε1 hεx E hElim`. Establish `hEφ : comp1 E φ = φ`. Use function extensionality and compare the values at `i`. Establish `L` using `TendsS.comp1 (φ := fun n => Y.B.A.act (1 * ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (fun n => act0 _) hφ0 hET hT i`.

Establish `hdiv : ∀ n, ((V.l : O) ^ (n + 1)) ∣ (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n`. Introduce `n`. Establish `e1 : (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n = M n * (ε ^ V.l ^ n * ε ^ V.l ^ n - ε ^ V.l ^ n)` using `by ring`. Rewrite using `[e1]`. Conclude with `dvd_mul_of_dvd_right (sq_cong hε n) _`.

Establish `R` using `tendsS_of_small RowTiePLSmall.lSmall_holds Y (x := fun n => (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) (x' := fun n => M n * ε ^ V.l ^ n) hdiv hT i`. Establish `eq : (fun n => comp1 (Y.B.A.act (1 * ε ^ V.l ^ n)) (Y.B.A.act (M n * ε ^ V.l ^ n)) i) = fun n => Y.B.A.act ((1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) i` using `funext fun n => by`. Rewrite using `[Y.B.A.mul_act (1 * ε ^ V.l ^ n) (M n * ε ^ V.l ^ n)]`. Rewrite `L` using `[eq]`. Conclude with `L.unique R`.

Introduce `v`. Take `⟨b, hb⟩` from `hEspan (linAct φ v)`. Conclude with `⟨b, by rw [← hb, ← VP.linAct_comp1 E φ hφ0, hEφ]⟩`.
-/
theorem half [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (M : ℕ → O) (φ : Pt C 1 dd)
    (hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i)) :
    (∀ a, comp1 φ (Y.B.A.act a) = comp1 (Y.B.A.act a) φ) ∧
      ∀ v : Fin dd → C, ∃ b : I0 → C, linAct φ v = ∑ c, b c • p.e c := by
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨?_, ?_⟩
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
      (fun n => act0 _) hφ0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (M n * ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (M n * ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R
  · obtain ⟨E, -, -, -, hET⟩ := StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx (fun _ => 1)
      (fun N a => by rw [sub_self, map_zero]; exact VF.Ge.zero _)
    have hElim : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (E i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i)) := by
      intro N i μ
      obtain ⟨n0, h⟩ := hET i μ N
      exact ⟨n0, fun n hn => by simpa only [one_mul] using h n hn⟩
    have hEspan := hLie C V O dd Y d I0 p ε hε hε1 hεx E hElim
    have hEφ : comp1 E φ = φ := by
      funext i
      have L := TendsS.comp1 (φ := fun n => Y.B.A.act (1 * ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
        (fun n => act0 _) hφ0 hET hT i
      have hdiv : ∀ n, ((V.l : O) ^ (n + 1)) ∣ (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n := by
        intro n
        have e1 : (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n =
            M n * (ε ^ V.l ^ n * ε ^ V.l ^ n - ε ^ V.l ^ n) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right (sq_cong hε n) _
      have R := tendsS_of_small RowTiePLSmall.lSmall_holds Y
        (x := fun n => (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) (x' := fun n => M n * ε ^ V.l ^ n) hdiv hT i
      have eq : (fun n => comp1 (Y.B.A.act (1 * ε ^ V.l ^ n)) (Y.B.A.act (M n * ε ^ V.l ^ n)) i) =
          fun n => Y.B.A.act ((1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) i := funext fun n => by
        rw [Y.B.A.mul_act (1 * ε ^ V.l ^ n) (M n * ε ^ V.l ^ n)]
      rw [eq] at L
      exact L.unique R
    intro v
    obtain ⟨b, hb⟩ := hEspan (linAct φ v)
    exact ⟨b, by rw [← hb, ← VP.linAct_comp1 E φ hφ0, hEφ]⟩

/- English proof (translation)
Take `⟨ε, hε, hε1, hεx⟩` from `p.em_unr`. Establish `hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (M (N + 1) - M N))`. Introduce `N a`. Establish `e2 : p.em a (M (N + 1) - M N) = (t a - p.em a (M N)) - (t a - p.em a (M (N + 1)))`. Rewrite using `[map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `(hMt N a).sub ((hMt (N + 1) a).mono (by push_cast; linarith))`. Establish `ht : ∀ a, Tends V (fun n => p.em a (M n)) (t a)` using `fun a => tends_of_nat fun N => ⟨N, fun n hn => (hMt n a).mono (by`. Establish `: (N : ℝ) ≤ n` using `by exact_mod_cast hn`.

Use `push_cast`. Use the proof step `linarith)⟩`. Establish `hεs` using `star_rel hε`. Establish `hεs1 : ∀ a, V.MM (p.em a (star ε) - 1)` using `fun a => by rw [p.em_conj]; exact hε1 _`. Establish `hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y`.

Introduce `x hx`. Take `⟨y, hy⟩` from `hεx (star x) fun a => by rw [p.em_conj]; exact hx (a + p.hd)`. Use `⟨star y, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg star hy`. Simplify using `only [star_mul, star_star, star_natCast] at h`.

Rewrite using `[mul_comm, h, mul_comm]`. Establish `hMs : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (star (M (N + 1)) - star (M N)))` using `fun N a => by`. Rewrite using `[← star_sub, p.em_conj]`. Conclude with `hM N (a + p.hd)`. Establish `cvA` using `StartSelf.actCv_of Y p.em ε hε (fun a => p.em_int a ε) hεx M hM`.

Establish `cvB` using `StartSelf.actCv_of Y p.em (star ε) hεs (fun a => p.em_int a _) hεsx (fun N => star (M N)) hMs`. Establish `sA : (fun n => star (M n * ε ^ V.l ^ n)) = fun n => star (M n) * star ε ^ V.l ^ n`. Use function extensionality and compare the values at `fun n => by rw [star_mul', star_pow]`. Establish `sB : (fun n => star (star (M n) * star ε ^ V.l ^ n)) = fun n => M n * ε ^ V.l ^ n`. Use function extensionality and compare the values at `fun n => by rw [star_mul', star_pow, star_star, star_star]`.

Take `⟨γ, γb, hγI, -, hγl, hγbl, hhom, hexp⟩` from `endomorphism_limit_integral Y (fun n => M n * ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)`. Take `⟨γ2, -, hγ2I, -, hγ2l, -, hhom2, -⟩` from `endomorphism_limit_integral Y (fun n => star (M n) * star ε ^ V.l ^ n) cvB (by rw [sB]; exact cvA)`. Establish `hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (γ i)` using `tends_of_endomorphism_limit Y hγl`. Establish `hTb : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γb i)`. Establish `h` using `tends_of_endomorphism_limit Y hγbl`.

Simplify `h` using `only [star_mul', star_pow]`. Establish `hT2 : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γ2 i)` using `tends_of_endomorphism_limit Y hγ2l`. Establish `heq : γ2 = γb` using `funext fun i => (hT2 i).unique (hTb i)`. Substitute `heq` using the available equality. Take `⟨hc, hi⟩` from `half hLie Y p ε hε hε1 hεx M γ hT`.

Take `⟨hc', hi'⟩` from `half hLie Y p (star ε) hεs hεs1 hεsx (fun N => star (M N)) γ2 hT2`. Use `⟨γ, γ2, ⟨hγI, const_of_lim Y hT, hhom⟩, ⟨hγ2I, const_of_lim Y hT2, hhom2⟩, hc, hc', ?_, ?_, hi, hi', hexp⟩` and prove the remaining obligations. Conclude with `fun c => StartSelf.lin_of_lim Y p M ε hε1 t ht γ hT c`. Conclude with `fun c => StartSelf.lin_of_lim Y p (fun N => star (M N)) (star ε) hεs1 (fun a => t (a + p.hd)) (fun a => by simp only [p.em_conj]; exact ht (a + p.hd)) γ2 hT2 c`.
-/
theorem one_entry [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (M : ℕ → O) (t : ZMod d → C) (hMt : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (t a - p.em a (M N))) :
    ∃ γ γ' : Pt C 1 dd, IsEndo Y γ ∧ IsEndo Y γ' ∧
      (∀ a, comp1 γ (Y.B.A.act a) = comp1 (Y.B.A.act a) γ) ∧
      (∀ a, comp1 γ' (Y.B.A.act a) = comp1 (Y.B.A.act a) γ') ∧
      (∀ c, linAct γ (p.e c) = t (p.ty0 c) • p.e c) ∧
      (∀ c, linAct γ' (p.e c) = t (p.ty0 c + p.hd) • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ v = ∑ c, b c • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ' v = ∑ c, b c • p.e c) ∧
      IntS V (FB.expS C (ev (n := 2) ![comp1 γ (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 γ' (pt C dd 1)] Y.h)) := by
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr
  have hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (M (N + 1) - M N)) := by
    intro N a
    have e2 : p.em a (M (N + 1) - M N) = (t a - p.em a (M N)) - (t a - p.em a (M (N + 1))) := by
      rw [map_sub]; ring
    rw [e2]
    exact (hMt N a).sub ((hMt (N + 1) a).mono (by push_cast; linarith))
  have ht : ∀ a, Tends V (fun n => p.em a (M n)) (t a) := fun a =>
    tends_of_nat fun N => ⟨N, fun n hn => (hMt n a).mono (by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith)⟩
  have hεs := star_rel hε
  have hεs1 : ∀ a, V.MM (p.em a (star ε) - 1) := fun a => by rw [p.em_conj]; exact hε1 _
  have hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [p.em_conj]; exact hx (a + p.hd)
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have hMs : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (star (M (N + 1)) - star (M N))) := fun N a => by
    rw [← star_sub, p.em_conj]; exact hM N (a + p.hd)
  have cvA := StartSelf.actCv_of Y p.em ε hε (fun a => p.em_int a ε) hεx M hM
  have cvB := StartSelf.actCv_of Y p.em (star ε) hεs (fun a => p.em_int a _) hεsx (fun N => star (M N)) hMs
  have sA : (fun n => star (M n * ε ^ V.l ^ n)) = fun n => star (M n) * star ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow]
  have sB : (fun n => star (star (M n) * star ε ^ V.l ^ n)) = fun n => M n * ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow, star_star, star_star]
  obtain ⟨γ, γb, hγI, -, hγl, hγbl, hhom, hexp⟩ := endomorphism_limit_integral Y (fun n => M n * ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  obtain ⟨γ2, -, hγ2I, -, hγ2l, -, hhom2, -⟩ := endomorphism_limit_integral Y (fun n => star (M n) * star ε ^ V.l ^ n) cvB
    (by rw [sB]; exact cvA)
  have hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (γ i) := tends_of_endomorphism_limit Y hγl
  have hTb : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γb i) := by
    have h := tends_of_endomorphism_limit Y hγbl
    simpa only [star_mul', star_pow] using h
  have hT2 : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γ2 i) := tends_of_endomorphism_limit Y hγ2l
  have heq : γ2 = γb := funext fun i => (hT2 i).unique (hTb i)
  subst heq
  obtain ⟨hc, hi⟩ := half hLie Y p ε hε hε1 hεx M γ hT
  obtain ⟨hc', hi'⟩ := half hLie Y p (star ε) hεs hεs1 hεsx (fun N => star (M N)) γ2 hT2
  refine ⟨γ, γ2, ⟨hγI, const_of_lim Y hT, hhom⟩, ⟨hγ2I, const_of_lim Y hT2, hhom2⟩, hc, hc', ?_, ?_, hi, hi', hexp⟩
  · exact fun c => StartSelf.lin_of_lim Y p M ε hε1 t ht γ hT c
  · exact fun c => StartSelf.lin_of_lim Y p (fun N => star (M N)) (star ε) hεs1 (fun a => t (a + p.hd))
      (fun a => by simp only [p.em_conj]; exact ht (a + p.hd)) γ2 hT2 c

end GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

/- English proof (translation)
Use `choose Mm hMm using fun N : ℕ => p.gm_lim (N + 1)`. Apply the tactic sequence `have h := fun r s : Fin 2 => GmPackP.one_entry hLie Y p (fun N => Mm N r s) (fun a => p.gm a r s) (fun N a => hMm N a r s)`. Use `choose γ γ' h1 h2 h3 h4 h5 h6 h7 h8 h9 using h`. Conclude with `⟨γ, γ', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩`.
-/
theorem gmPack_of_lie [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := by
  choose Mm hMm using fun N : ℕ => p.gm_lim (N + 1)
  have h := fun r s : Fin 2 => GmPackP.one_entry hLie Y p (fun N => Mm N r s) (fun a => p.gm a r s)
    (fun N a => hMm N a r s)
  choose γ γ' h1 h2 h3 h4 h5 h6 h7 h8 h9 using h
  exact ⟨γ, γ', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

/- English proof (translation)
The claim follows from `gmPack_of_lie (projLieSelf_of hE) Y p`.
-/
theorem gmPack_of [NeZero d] (hE : RowTiePKey.KeyEigSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := gmPack_of_lie (projLieSelf_of hE) Y p

/- English proof (translation)
The claim follows from `gmPack_of RowTiePKey.keyEig_holds Y p`.
-/
theorem gmPack_holds [NeZero d] (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    GmPackSt Y p := gmPack_of RowTiePKey.keyEig_holds Y p

end Formalism.L2.FormalSeriesBounds
