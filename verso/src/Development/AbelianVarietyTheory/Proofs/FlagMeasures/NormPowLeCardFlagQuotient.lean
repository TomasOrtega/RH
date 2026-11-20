import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPartnerLift

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.LoopC.AdmissibleOrder

open GlobalTheory.LoopC.Partner

/- English proof (translation)
Assume the negation of the conclusion as `h1`. Establish `hJ : J ≠ ⊤` using `fun hJ => h1 (hJ ▸ Submodule.mem_top)`. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal J hJ`. Establish `hM0 : M ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)`. Take `⟨s, hsJ, hsM⟩` from `h ⟨M, hM.isPrime, hM0⟩ (hJM hg)`.

Conclude with `hsM (hJM hsJ)`.
-/
theorem one_mem_of_local {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (J : Ideal (𝓞 E)) (hg : g ∈ J)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s ∈ J, s ∉ P.asIdeal) : (1 : 𝓞 E) ∈ J := by
  by_contra h1
  have hJ : J ≠ ⊤ := fun hJ => h1 (hJ ▸ Submodule.mem_top)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)
  obtain ⟨s, hsJ, hsM⟩ := h ⟨M, hM.isPrime, hM0⟩ (hJM hg)
  exact hsM (hJM hsJ)

/- English proof (translation)
Establish `key : ∀ c c' : Fin n → R, ∑ b, c b • q b = ∑ b, c' b • q b → ∀ b, Ideal.Quotient.mk I (c b) = Ideal.Quotient.mk I (c' b)`. Introduce `c c' hcc b`. Rewrite using `[Ideal.Quotient.eq]`. Establish `hz : ∑ b, (c - c') b • q b = 0`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcc, sub_self]`.

Simplify using `using h (c - c') hz b`. Set `f : Q → (Fin n → R ⧸ I)` to `fun x => if hx : ∃ c : Fin n → R, ∑ b, c b • q b = x then fun b => Ideal.Quotient.mk I (hx.choose b) else 0`. Establish `hf : Function.Surjective f`. Introduce `t`. Use `choose c hc using fun b => Ideal.Quotient.mk_surjective (I := I) (t b)`.

Establish `hx : ∃ c' : Fin n → R, ∑ b, c' b • q b = ∑ b, c b • q b` using `⟨c, rfl⟩`. Use `⟨∑ b, c b • q b, ?_⟩` and prove the remaining obligations. Simplify using `only [f, dif_pos hx]`. Use function extensionality and compare the values at `b`. Rewrite using `[key _ c hx.choose_spec b, hc]`.

Establish `hle` using `Nat.card_le_card_of_surjective f hf`. Simplify `hle` using `[Nat.card_fun]`.
-/
theorem pow_card_le {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] [Finite Q] (I : Ideal R) {n : ℕ}
    (q : Fin n → Q) (h : ∀ c : Fin n → R, ∑ b, c b • q b = 0 → ∀ b, c b ∈ I) :
    Nat.card (R ⧸ I) ^ n ≤ Nat.card Q := by
  have key : ∀ c c' : Fin n → R, ∑ b, c b • q b = ∑ b, c' b • q b →
      ∀ b, Ideal.Quotient.mk I (c b) = Ideal.Quotient.mk I (c' b) := by
    intro c c' hcc b
    rw [Ideal.Quotient.eq]
    have hz : ∑ b, (c - c') b • q b = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcc, sub_self]
    simpa using h (c - c') hz b
  let f : Q → (Fin n → R ⧸ I) := fun x =>
    if hx : ∃ c : Fin n → R, ∑ b, c b • q b = x then fun b => Ideal.Quotient.mk I (hx.choose b) else 0
  have hf : Function.Surjective f := by
    intro t
    choose c hc using fun b => Ideal.Quotient.mk_surjective (I := I) (t b)
    have hx : ∃ c' : Fin n → R, ∑ b, c' b • q b = ∑ b, c b • q b := ⟨c, rfl⟩
    refine ⟨∑ b, c b • q b, ?_⟩
    simp only [f, dif_pos hx]
    funext b
    rw [key _ c hx.choose_spec b, hc]
  have hle := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_fun] using hle

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

/- English proof (translation)
Establish `hlast : T' * b (Fin.last r) = 0`. Establish `h0` using `hT_fvec_sum F' b (Fin.last r)`. Rewrite `h0` using `[hb, map_zero]`. Simplify using `using h0.symm`. Establish `hZ : (Zhat F F').mulVec b = Pi.single (Fin.last r) (T * (0 : Fin (r + 1) → E) (Fin.last r))`.

Use function extensionality and compare the values at `i`. Establish `h0 : S.hT (F.fvec i) (∑ j, b j • F'.fvec j) = 0` using `by rw [hb, map_zero]`. Rewrite `h0` using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul] at h0`. Simplify using `only [Pi.zero_apply, mul_zero, Pi.single_zero]`.

Rewrite using `[← h0]`. Simplify using `only [Matrix.mulVec, dotProduct, Zhat, brS]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `h2 : (Zhat F F').conjTranspose.mulVec (0 : Fin (r + 1) → E) = Pi.single (Fin.last r) (T' * b (Fin.last r))`. Rewrite using `[hlast, Matrix.mulVec_zero, Pi.single_zero]`.

Establish `hd1 : Dl F F' (r + 1) = (Zhat F F').det`. Unfold `Dl leadMinorE`. Rewrite using `[dif_pos le_rfl]`. Use `congr 1`. Establish `hd0 : Dl F F' r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det`.

Unfold `Dl leadMinorE`. Rewrite using `[dif_pos (Nat.le_succ r)]`. Use `congr 1`. Establish `hG'` using `hG`. Unfold `Gflag at hG'`.

Rewrite `hG'` using `[hd1, hd0]`. Conclude with `(pair_eq_zero (Zhat F F') 0 b T T' hG' hZ h2).2`.
-/
theorem frame_indep (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (b : Fin (r + 1) → E)
    (hb : ∑ j, b j • F'.fvec j = 0) : b = 0 := by
  have hlast : T' * b (Fin.last r) = 0 := by
    have h0 := hT_fvec_sum F' b (Fin.last r)
    rw [hb, map_zero] at h0
    simpa using h0.symm
  have hZ : (Zhat F F').mulVec b = Pi.single (Fin.last r) (T * (0 : Fin (r + 1) → E) (Fin.last r)) := by
    funext i
    have h0 : S.hT (F.fvec i) (∑ j, b j • F'.fvec j) = 0 := by rw [hb, map_zero]
    rw [map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    simp only [Pi.zero_apply, mul_zero, Pi.single_zero]
    rw [← h0]
    simp only [Matrix.mulVec, dotProduct, Zhat, brS]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h2 : (Zhat F F').conjTranspose.mulVec (0 : Fin (r + 1) → E) = Pi.single (Fin.last r) (T' * b (Fin.last r)) := by
    rw [hlast, Matrix.mulVec_zero, Pi.single_zero]
  have hd1 : Dl F F' (r + 1) = (Zhat F F').det := by
    unfold Dl leadMinorE
    rw [dif_pos le_rfl]
    congr 1
  have hd0 : Dl F F' r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det := by
    unfold Dl leadMinorE
    rw [dif_pos (Nat.le_succ r)]
    congr 1
  have hG' := hG
  unfold Gflag at hG'
  rw [hd1, hd0] at hG'
  exact (pair_eq_zero (Zhat F F') 0 b T T' hG' hZ h2).2

variable {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Use `set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)} • Λ).colon {x} with hJ`. Establish `hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ` using `fun s => Submodule.mem_colon_singleton`. Establish `h1 : (1 : 𝓞 E) ∈ J`. Use `one_mem_of_local (g : 𝓞 E) J ((hmem _).2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx)) ?_` and prove the remaining obligations. Introduce `P hP`.

Take `⟨s, hs, hsx⟩` from `h P hP`. Conclude with `⟨s, (hmem s).2 hsx, hs⟩`. Establish `hx1` using `(hmem 1).1 h1`. Rewrite `hx1` using `[one_smul, Submodule.ideal_span_singleton_smul]`. Take `⟨w, hw, hwx⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx1`.

Conclude with `⟨w, hw, hwx⟩`.
-/
theorem exists_div {g : ℕ} {x : S.V} (hx : x ∈ Λ) (h : ModG S Λ g x) : ∃ w ∈ Λ, (g : 𝓞 E) • w = x := by
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)} • Λ).colon {x} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ := fun s =>
    Submodule.mem_colon_singleton
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J
      ((hmem _).2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx)) ?_
    intro P hP
    obtain ⟨s, hs, hsx⟩ := h P hP
    exact ⟨s, (hmem s).2 hsx, hs⟩
  have hx1 := (hmem 1).1 h1
  rw [one_smul, Submodule.ideal_span_singleton_smul] at hx1
  obtain ⟨w, hw, hwx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx1
  exact ⟨w, hw, hwx⟩

/- English proof (translation)
Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hq`. Take `⟨o, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Use `set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)}).colon {c b} with hJ`. Establish `hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • c b ∈ Ideal.span {(g : 𝓞 E)}` using `fun s => Submodule.mem_colon_singleton`. Establish `key : ∀ s : 𝓞 E, s • x ∈ Submodule.span (𝓞 E) (Set.range F.fl.e) → s ∈ J`.

Introduce `s hs`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs`. Set `d' : Fin (r + 1) → 𝓞 E` to `Fin.snoc (α := fun _ => 𝓞 E) d (s * o)`. Establish `e1 : ∑ j, d' j • frame F j = s • x + (s * o) • F.zt`. Rewrite using `[Fin.sum_univ_castSucc]`.

Simplify using `only [d', frame, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last, hd, hL.2]`. Establish `hsum : ∑ j, ((s * c j - (g : 𝓞 E) * d' j : 𝓞 E) : E) • frame F j = 0`. Simplify using `only [smul_coe]`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, mul_smul]`. Rewrite using `[← Finset.smul_sum, ← Finset.smul_sum, h, e1]`.

Use `module`. Establish `hb0 : ((s * c b - (g : 𝓞 E) * d' b : 𝓞 E) : E) = 0` using `congrFun (hind _ hsum) b`. Establish `hb1 : s * c b = (g : 𝓞 E) * d' b`. Rewrite using `[← sub_eq_zero]`. Conclude with `hb0` after adjusting the coercions.

Rewrite using `[hmem, smul_eq_mul, hb1]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Establish `h1 : (1 : 𝓞 E) ∈ J`. Use `one_mem_of_local (g : 𝓞 E) J ?_ ?_` and prove the remaining obligations. Rewrite using `[hmem, smul_eq_mul]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Introduce `P hP`. Take `⟨cc, -, hc1, hloc⟩` from `hC.1 P`. Establish `hx' : x ∈ (haveI` using `P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) := by show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ XLam Λ F`. Conclude with `⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩`.

Rewrite `hx'` using `[hloc]`. Take `⟨s, hs, hsx⟩` from `hx'`. Use `⟨s, key s ?_, hs⟩` and prove the remaining obligations. Establish `hfun : (fun a => cc a • F.fl.e a) = F.fl.e` using `funext fun a => by rw [hc1 hP a, one_smul]`. Rewrite `hsx` using `[hfun]`. Then use the resulting hypothesis.

Simplify using `using (hmem 1).1 h1`.
-/
theorem coeff_mem {g : ℕ} (F : LFlag S r T) (hL : IsLift Λ F) (hC : IsFixedConv Λ g F)
    (hind : ∀ b : Fin (r + 1) → E, ∑ j, b j • frame F j = 0 → b = 0) (c : Fin (r + 1) → 𝓞 E) {q : S.V}
    (hq : q ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt}) (h : ∑ j, c j • frame F j = (g : 𝓞 E) • q) (b : Fin (r + 1)) :
    c b ∈ Ideal.span {(g : 𝓞 E)} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hq
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)}).colon {c b} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • c b ∈ Ideal.span {(g : 𝓞 E)} := fun s =>
    Submodule.mem_colon_singleton
  have key : ∀ s : 𝓞 E, s • x ∈ Submodule.span (𝓞 E) (Set.range F.fl.e) → s ∈ J := by
    intro s hs
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs
    let d' : Fin (r + 1) → 𝓞 E := Fin.snoc (α := fun _ => 𝓞 E) d (s * o)
    have e1 : ∑ j, d' j • frame F j = s • x + (s * o) • F.zt := by
      rw [Fin.sum_univ_castSucc]
      simp only [d', frame, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last, hd, hL.2]
    have hsum : ∑ j, ((s * c j - (g : 𝓞 E) * d' j : 𝓞 E) : E) • frame F j = 0 := by
      simp only [smul_coe]
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [← Finset.smul_sum, ← Finset.smul_sum, h, e1]
      module
    have hb0 : ((s * c b - (g : 𝓞 E) * d' b : 𝓞 E) : E) = 0 := congrFun (hind _ hsum) b
    have hb1 : s * c b = (g : 𝓞 E) * d' b := by
      rw [← sub_eq_zero]
      exact_mod_cast hb0
    rw [hmem, smul_eq_mul, hb1]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J ?_ ?_
    · rw [hmem, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro P hP
      obtain ⟨cc, -, hc1, hloc⟩ := hC.1 P
      have hx' : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) := by
        show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ XLam Λ F
        exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
      rw [hloc] at hx'
      obtain ⟨s, hs, hsx⟩ := hx'
      refine ⟨s, key s ?_, hs⟩
      have hfun : (fun a => cc a • F.fl.e a) = F.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
      rwa [hfun] at hsx
  simpa using (hmem 1).1 h1

/- English proof (translation)
Introduce `E _ _ _ S r Λ g T T' F F' hg hL hL' hF hF' hC' hAdm hGv hfin`. Take `⟨ξ, -, -, hξ⟩` from `hAdm`. Establish `hfX : ∀ b, frameAct (frame F) ξ b ∈ Xplus F` using `fun b => (mem_Xplus_iff F.fl _).2 ⟨fun a => ((ξ a b : 𝓞 E) : E), rfl⟩`. Establish `hf'X : ∀ b, frame F' b ∈ Xplus F'` using `fun b => (mem_Xplus_iff F'.fl _).2 ⟨Pi.single b 1, by simp [Pi.single_apply, ite_smul]⟩`. Establish `hxΛ : ∀ b, frame F' b - frameAct (frame F) ξ b ∈ Λ`.

Introduce `b`. Use `Λ.sub_mem (hF' b) (Λ.sum_mem fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_coe]`. Conclude with `Λ.smul_mem _ (hF a)`. Use `choose w hwΛ hw using fun b => exists_div (hxΛ b) (hξ b)`.

Establish `hgE : (g : E) ≠ 0` using `Nat.cast_ne_zero.2 hg`. Establish `hwB : ∀ b, w b ∈ BLat Λ F F'`. Introduce `b`. Use `Submodule.mem_inf.2 ⟨hwΛ b, ?_⟩` and prove the remaining obligations. Use `show w b ∈ UUE Λ F F'`.

Rewrite using `[UUE_eq F F' hL hL' hF hF']`. Establish `hwb : w b = (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)`. Rewrite using `[← hw b, ← smul_coe, smul_smul]`. Establish `hc : (((g : 𝓞 E) : E)) = (g : E)` using `by simp`. Rewrite using `[hc, inv_mul_cancel₀ hgE, one_smul]`.

Rewrite using `[hwb]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right (hf'X b)) (Submodule.mem_sup_left (hfX b)))`. Establish `_hfin` using `hfin`. Set `q : Fin (r + 1) → BQ Λ F F'` to `fun b => Submodule.Quotient.mk ⟨w b, hwB b⟩`. Establish `key : ∀ c : Fin (r + 1) → 𝓞 E, ∑ b, c b • q b = 0 → ∀ b, c b ∈ Ideal.span {(g : 𝓞 E)}`.

Introduce `c hc`. Establish `hc' : ∑ b, c b • w b ∈ UU Λ F F'`. Establish `h0 : (Submodule.mkQ ((UU Λ F F').comap (BLat Λ F F').subtype)) (∑ b, c b • (⟨w b, hwB b⟩ : BLat Λ F F')) = 0`. Rewrite using `[map_sum]`. Simplify `hc` using `only [map_smul, Submodule.mkQ_apply, q]`.

Rewrite `h0` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Simplify using `using h0`. Rewrite `hc'` using `[UU_eq]`. Take `⟨u, hu, u', hu', huu⟩` from `Submodule.mem_sup.1 hc'`. Establish `hgsum : ∑ b, c b • (frame F' b - frameAct (frame F) ξ b) = (g : 𝓞 E) • u + (g : 𝓞 E) • u'`.

Rewrite using `[← smul_add, huu, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← hw b, smul_comm]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib] at hgsum`. Establish `hA : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' = ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hgsum]`. Use `_ = ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by abel`. Establish `huX : u ∈ Xplus F` using `(Submodule.mem_inf.1 (half_le F hL hu)).2`. Establish `hu'X : u' ∈ Xplus F'` using `(Submodule.mem_inf.1 (half_le F' hL' hu')).2`.

Establish `hmF' : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ Xplus F'` using `Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hf'X b)) (Submodule.smul_of_tower_mem _ _ hu'X)`. Establish `hmF : ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u ∈ Xplus F` using `Submodule.add_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hfX b)) (Submodule.smul_of_tower_mem _ _ huX)`. Establish `hm : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ F.fl.Xplus ⊓ F'.fl.Xplus` using `Submodule.mem_inf.2 ⟨hA ▸ hmF, hmF'⟩`. Rewrite `hm` using `[Xplus_inf F.fl F'.fl hGv]`. Establish `hfin2 : ∑ b, c b • frame F' b = (g : 𝓞 E) • u'` using `sub_eq_zero.1 ((Submodule.mem_bot E).1 hm)`.

Conclude with `coeff_mem F' hL' hC' (fun b hb => frame_indep F.fl F'.fl hGv b hb) c hu' hfin2`. Establish `hcard` using `pow_card_le (Ideal.span {(g : 𝓞 E)}) q key`. Establish `hN : ((Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) : ℕ) : ℝ) = NE (E` using `E) g := by`. Establish `hn` using `Ideal.absNorm_span_singleton ((g : 𝓞 E))`. Rewrite `hn` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Rewrite using `[hn, NE]`. Establish `hg' : ((g : 𝓞 E)) = algebraMap ℤ (𝓞 E) (g : ℤ)` using `by simp`. Rewrite using `[hg', Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]`. Simplify using the standard rewrite rules. Rewrite using `[← hN]`.

Conclude with `hcard` after adjusting the coercions.
-/
theorem NE_pow_le_card_BQ : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  intro E _ _ _ S r Λ g T T' F F' hg hL hL' hF hF' hC' hAdm hGv hfin
  obtain ⟨ξ, -, -, hξ⟩ := hAdm
  have hfX : ∀ b, frameAct (frame F) ξ b ∈ Xplus F :=
    fun b => (mem_Xplus_iff F.fl _).2 ⟨fun a => ((ξ a b : 𝓞 E) : E), rfl⟩
  have hf'X : ∀ b, frame F' b ∈ Xplus F' := fun b =>
    (mem_Xplus_iff F'.fl _).2 ⟨Pi.single b 1, by simp [Pi.single_apply, ite_smul]⟩
  have hxΛ : ∀ b, frame F' b - frameAct (frame F) ξ b ∈ Λ := by
    intro b
    refine Λ.sub_mem (hF' b) (Λ.sum_mem fun a _ => ?_)
    rw [smul_coe]
    exact Λ.smul_mem _ (hF a)
  choose w hwΛ hw using fun b => exists_div (hxΛ b) (hξ b)
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have hwB : ∀ b, w b ∈ BLat Λ F F' := by
    intro b
    refine Submodule.mem_inf.2 ⟨hwΛ b, ?_⟩
    show w b ∈ UUE Λ F F'
    rw [UUE_eq F F' hL hL' hF hF']
    have hwb : w b = (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b) := by
      rw [← hw b, ← smul_coe, smul_smul]
      have hc : (((g : 𝓞 E) : E)) = (g : E) := by simp
      rw [hc, inv_mul_cancel₀ hgE, one_smul]
    rw [hwb]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.mem_sup_right (hf'X b)) (Submodule.mem_sup_left (hfX b)))
  have _hfin := hfin
  let q : Fin (r + 1) → BQ Λ F F' := fun b => Submodule.Quotient.mk ⟨w b, hwB b⟩
  have key : ∀ c : Fin (r + 1) → 𝓞 E, ∑ b, c b • q b = 0 → ∀ b, c b ∈ Ideal.span {(g : 𝓞 E)} := by
    intro c hc
    have hc' : ∑ b, c b • w b ∈ UU Λ F F' := by
      have h0 : (Submodule.mkQ ((UU Λ F F').comap (BLat Λ F F').subtype))
          (∑ b, c b • (⟨w b, hwB b⟩ : BLat Λ F F')) = 0 := by
        rw [map_sum]
        simpa only [map_smul, Submodule.mkQ_apply, q] using hc
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
      simpa using h0
    rw [UU_eq] at hc'
    obtain ⟨u, hu, u', hu', huu⟩ := Submodule.mem_sup.1 hc'
    have hgsum : ∑ b, c b • (frame F' b - frameAct (frame F) ξ b) = (g : 𝓞 E) • u + (g : 𝓞 E) • u' := by
      rw [← smul_add, huu, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hw b, smul_comm]
    simp only [smul_sub, Finset.sum_sub_distrib] at hgsum
    have hA : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' =
        ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by
      calc ∑ b, c b • frame F' b - (g : 𝓞 E) • u'
          = (∑ b, c b • frame F' b - ∑ b, c b • frameAct (frame F) ξ b) +
              ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by abel
        _ = ((g : 𝓞 E) • u + (g : 𝓞 E) • u') + ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by
              rw [hgsum]
        _ = ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by abel
    have huX : u ∈ Xplus F := (Submodule.mem_inf.1 (half_le F hL hu)).2
    have hu'X : u' ∈ Xplus F' := (Submodule.mem_inf.1 (half_le F' hL' hu')).2
    have hmF' : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ Xplus F' :=
      Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hf'X b))
        (Submodule.smul_of_tower_mem _ _ hu'X)
    have hmF : ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u ∈ Xplus F :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hfX b))
        (Submodule.smul_of_tower_mem _ _ huX)
    have hm : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ F.fl.Xplus ⊓ F'.fl.Xplus :=
      Submodule.mem_inf.2 ⟨hA ▸ hmF, hmF'⟩
    rw [Xplus_inf F.fl F'.fl hGv] at hm
    have hfin2 : ∑ b, c b • frame F' b = (g : 𝓞 E) • u' := sub_eq_zero.1 ((Submodule.mem_bot E).1 hm)
    exact coeff_mem F' hL' hC' (fun b hb => frame_indep F.fl F'.fl hGv b hb) c hu' hfin2
  have hcard := pow_card_le (Ideal.span {(g : 𝓞 E)}) q key
  have hN : ((Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) : ℕ) : ℝ) = NE (E := E) g := by
    have hn := Ideal.absNorm_span_singleton ((g : 𝓞 E))
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    rw [hn, NE]
    have hg' : ((g : 𝓞 E)) = algebraMap ℤ (𝓞 E) (g : ℤ) := by simp
    rw [hg', Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  rw [← hN]
  exact_mod_cast hcard

end GlobalTheory.LoopC.AdmissibleOrder
