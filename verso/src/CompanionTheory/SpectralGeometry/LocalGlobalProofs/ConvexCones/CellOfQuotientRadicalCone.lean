import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical

/- English proof (translation)
Introduce `O _ _ _ _ bar _hCM ψ X _ _ _ hface β _hβ _hβpsd m γ hcell hcone`. Establish `mem_bal : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (f : LinearMap.BilinForm ℤ Y), f ∈ GlobalTheory.PolFan.balForms bar Y ↔ ((∀ y z, f y z = f z y) ∧ ∀ (a : O) (y z : Y), f (a • y) z = f y (bar a • z))` using `fun _ => Iff.rfl`. Establish `psd_zero : ∀ f : LinearMap.BilinForm ℤ X, f ∈ GlobalTheory.PolFan.balForms bar X → (∀ y, 0 ≤ f y y) → ∀ x, f x x = 0 → ∀ y, f x y = 0`. Introduce `f hf hfp x hx y`. Establish `hsym : f y x = f x y` using `((mem_bal f).1 hf).1 y x`.

Assume the negation of the conclusion as `hne`. Establish `expand : ∀ n : ℤ, f (n • x + y) (n • x + y) = n * n * f x x + n * f x y + n * f y x + f y y`. Introduce `n`. Simplify using `only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key` using `hfp ((-(f y y + 1) * f x y) • x + y)`. Rewrite `key` using `[expand, hx, hsym]`. Establish `h1 : 0 < f x y * f x y` using `mul_self_pos.2 hne`. Establish `h2 : 1 ≤ f x y * f x y` using `by simpa using Int.add_one_le_iff.2 h1`. Establish `h0` using `hfp y`.

Use polynomial arithmetic with `[mul_nonneg (by linarith : (0:ℤ) ≤ f y y + 1) (by linarith : (0:ℤ) ≤ f x y * f x y - 1)]`. Take `⟨c, hc0, hcsum⟩` from `hcone`. Establish `hval : ∀ x y, ((β x y : ℤ) : ℝ) = ∑ i, c i * ((γ i x y : ℤ) : ℝ)`. Introduce `x y`. Use `congrArg (fun L : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => L x y) hcsum` as an intermediate fact.

Simplify `this` using `[GlobalTheory.PolFan.toReal]`. Use `set K : Submodule O X := GlobalTheory.PolFan.CarDim.orad β with hK`. Establish `hKβ : ∀ x ∈ K, β x x = 0`. Introduce `x hx`. Use `(GlobalTheory.PolFan.CarDim.mem_orad (O := O)).1 hx 1 x` as an intermediate fact.

Simplify using `using this`. Set `P : Fin m → Prop` to `fun j => ∀ x ∈ K, ∀ y, γ j x y = 0`. Establish `hpos : ∀ j, 0 < c j → P j`. Introduce `j hcj x hx`. Apply `psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x` to reduce the goal to its premises.

Establish `hsum : ∑ i, c i * ((γ i x x : ℤ) : ℝ) = 0`. Rewrite using `[← hval, hKβ x hx]`. Simplify using the standard rewrite rules. Establish `hnn : ∀ i ∈ Finset.univ, 0 ≤ c i * ((γ i x x : ℤ) : ℝ)` using `fun i _ => mul_nonneg (hc0 i) (by exact_mod_cast hcell.nonneg i x)`. Establish `hz` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)`.

Break down `mul_eq_zero.1 hz with h | h` into its components or cases. Conclude with `absurd h hcj.ne'`. Conclude with `h` after adjusting the coercions. Establish `hw : ∀ j, ∃ x ∈ K, (¬ P j → 0 < γ j x x)`. Introduce `j`.

Distinguish the cases in `hj : P j`. Conclude with `⟨0, K.zero_mem, fun h => absurd hj h⟩`. Simplify using `only [P, not_forall] at hj`. Take `⟨x, hx, y, hxy⟩` from `hj`. Use `⟨x, hx, fun _ => ?_⟩` and prove the remaining obligations.

Break down `(hcell.nonneg j x).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x h.symm y) hxy`. Use `choose w hwK hwpos using hw`. Set `h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ` to `{ toFun := fun f => ∑ j, f (w j) (w j) map_add' := fun f g => by simp [Finset.sum_add_distrib] map_smul' := fun a f => by simp [Finset.mul_sum] }`.

Establish `hh : ∀ f, h f = ∑ j, f (w j) (w j)` using `fun _ => rfl`. Set `T : Finset (Fin m)` to `Finset.univ.filter P`. Set `s : Fin T.card ↪ Fin m` to `(T.orderEmbOfFin rfl).toEmbedding`. Establish `hsT : ∀ j, j ∈ Set.range s ↔ P j`. Introduce `j`.

Establish `hr : Set.range s = (T : Set (Fin m))` using `Finset.range_orderEmbOfFin T rfl`. Rewrite using `[hr]`. Simplify using `[T]`. Establish `hPs : ∀ i, P (s i)` using `fun i => (hsT (s i)).1 ⟨i, rfl⟩`. Establish `hfc : GlobalTheory.PolFan.IsFaceCut γ s h`.

Use `⟨fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hh]`. Conclude with `Finset.sum_nonneg fun i _ => hcell.nonneg j (w i)`. Rewrite using `[hsT, hh]`. Prove the components needed by the constructor for the conclusion.

Introduce `h0`. Assume the negation of the conclusion as `hj`. Establish `hnn : ∀ i ∈ Finset.univ, 0 ≤ γ j (w i) (w i)` using `fun i _ => hcell.nonneg j (w i)`. Use `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)` as an intermediate fact. Conclude with `(hwpos j hj).ne' this`.

Introduce `hj`. Conclude with `Finset.sum_eq_zero fun i _ => hj (w i) (hwK i) (w i)`. Establish `hcell'` using `hface m T.card γ s h hcell hfc`. Establish `hvanl : ∀ i, ∀ x ∈ K, ∀ y, γ (s i) x y = 0` using `fun i => hPs i`. Establish `hvanr : ∀ i, ∀ x y, y ∈ K → γ (s i) x y = 0`.

Introduce `i x y hy`. Rewrite using `[((mem_bal _).1 (hcell.mem (s i))).1 x y]`. Conclude with `hPs i y hy x`. Use `choose δ hδ using fun i => GlobalTheory.PolFan.CarDim.exists_pull_mkQ_eq_of_vanish K (γ (s i)) (hvanl i) (hvanr i)`. Establish `hr : Function.Surjective K.mkQ` using `K.mkQ_surjective`.

Establish `hδap : ∀ i x y, δ i (K.mkQ x) (K.mkQ y) = γ (s i) x y`. Introduce `i x y`. Rewrite using `[← hδ i]`. Both sides reduce to the same expression. Establish `heZ : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K), ψ.evalZ (GlobalTheory.PolFan.pull K.mkQ f) = ψ.evalZ f`.

Introduce `f`. Conclude with `ψ.eval_comp hr (fun a b => ((f a b : ℤ) : ℝ))`. Establish `hpullbal : ∀ f ∈ GlobalTheory.PolFan.balForms bar (X ⧸ K), GlobalTheory.PolFan.pull K.mkQ f ∈ GlobalTheory.PolFan.balForms bar X`. Introduce `f hf`. Take `⟨hs, hb⟩` from `(mem_bal f).1 hf`.

Use `(mem_bal _).2 ⟨fun y z => hs (K.mkQ y) (K.mkQ z), fun a y z => ?_⟩` and prove the remaining obligations. Use `show f (K.mkQ (a • y)) (K.mkQ z) = f (K.mkQ y) (K.mkQ (bar a • z))`. Rewrite using `[LinearMap.map_smul, LinearMap.map_smul]`. Conclude with `hb a (K.mkQ y) (K.mkQ z)`. Establish `hpullpsd : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K), (∀ q, 0 ≤ f q q) → ∀ y, 0 ≤ GlobalTheory.PolFan.pull K.mkQ f y y` using `fun f hf y => hf (K.mkQ y)`.

Establish `hfun : (fun i => GlobalTheory.PolFan.pull K.mkQ (δ i)) = fun i => γ (s i)` using `funext hδ`. Use `⟨T.card, δ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨fun i => ?_, fun i q => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(mem_bal _).2 ⟨fun a b => ?_, fun a u v => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hr a`.

Take `⟨y, rfl⟩` from `hr b`. Rewrite using `[hδap, hδap]`. Conclude with `((mem_bal _).1 (hcell.mem (s i))).1 x y`. Take `⟨x, rfl⟩` from `hr u`. Take `⟨y, rfl⟩` from `hr v`.

Rewrite using `[← LinearMap.map_smul, ← LinearMap.map_smul, hδap, hδap]`. Conclude with `((mem_bal _).1 (hcell.mem (s i))).2 a x y`. Take `⟨y, rfl⟩` from `hr q`. Rewrite using `[hδap]`. Conclude with `hcell.nonneg (s i) y`.

Introduce `c hc`. Establish `key` using `hcell'.linear.eval_eq_sum (X₁ := X ⧸ K) hr (B := fun a b => ∑ i, c i * ((δ i a b : ℤ) : ℝ)) hc (fun a b => by simp only [hδap])`. Rewrite using `[key]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show c i * ψ.evalZ (γ (s i)) = c i * ψ.evalZ (δ i)`.

Rewrite using `[← hδ i, heZ]`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hcell'.strict`. Use `⟨N, ℓ.comp (GlobalTheory.PolFan.CarDim.pullLin K.mkQ), hN, fun i => ?_, fun β' hb hp => ?_, fun β' hb hp heq => ?_⟩` and prove the remaining obligations. Establish `h1i : ((ℓ (γ (s i)) : ℤ) : ℝ) = (N : ℝ) * ψ.evalZ (γ (s i))` using `h1 i`. Rewrite using `[LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, hδ i, h1i, ← hδ i, heZ]`.

Rewrite using `[LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ]`. Conclude with `h2 _ (hpullbal β' hb) (hpullpsd β' hp)`. Rewrite `heq` using `[LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ]`. Take `⟨k, c', hk, hkc⟩` from `h3 _ (hpullbal β' hb) (hpullpsd β' hp) heq`. Use `⟨k, c', hk, ?_⟩` and prove the remaining obligations.

Establish `hkc' : k • GlobalTheory.PolFan.pull K.mkQ β' = ∑ i, c' i • γ (s i)` using `hkc`. Apply `GlobalTheory.PolFan.CarDim.pullLin_injective hr` to reduce the goal to its premises. Simplify using `only [map_nsmul, map_zsmul, LinearMap.map_smul_of_tower, map_sum, GlobalTheory.PolFan.CarDim.pullLin_apply]`. Rewrite using `[hkc']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hδ i]`. Rewrite using `[hfun]`. Simplify using `only [GlobalTheory.PolFan.InRCone]`. Use `⟨fun i => c (s i), fun i => hc0 _, ?_⟩` and prove the remaining obligations. Rewrite using `[hcsum]`.

Establish `hmap : Finset.univ.map s = T` using `Finset.map_orderEmbOfFin_univ T rfl`. Establish `e1 : (∑ i, c (s i) • GlobalTheory.PolFan.toReal (γ (s i))) = ∑ j ∈ T, c j • GlobalTheory.PolFan.toReal (γ j)`. Conclude with `(Finset.sum_map Finset.univ s (fun j => c j • GlobalTheory.PolFan.toReal (γ j))).symm.trans (by rw [hmap])`. Rewrite using `[e1]`. Use `symm`.

Apply `Finset.sum_filter_of_ne` to reduce the goal to its premises. Introduce `j _ hne`. Assume the negation of the conclusion as `hj`. Apply `hne` to reduce the goal to its premises. Establish `hcj : c j = 0`.

Break down `(hc0 j).lt_or_eq with h' | h'` into its components or cases. Conclude with `absurd (hpos j h') hj`. Conclude with `h'.symm`. Rewrite using `[hcj, zero_smul]`. Rewrite using `[← GlobalTheory.PolFan.CarDim.genRank_pull hr δ, hfun]`.

Unfold `GlobalTheory.PolFan.genRank`. Use `haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)`. Conclude with `Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range s γ))`.
-/
theorem exists_cell_quot_orad_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro O _ _ _ _ bar _hCM ψ X _ _ _ hface β _hβ _hβpsd m γ hcell hcone
  classical
  have mem_bal : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (f : LinearMap.BilinForm ℤ Y),
      f ∈ GlobalTheory.PolFan.balForms bar Y ↔
        ((∀ y z, f y z = f z y) ∧ ∀ (a : O) (y z : Y), f (a • y) z = f y (bar a • z)) :=
    fun _ => Iff.rfl
  have psd_zero : ∀ f : LinearMap.BilinForm ℤ X, f ∈ GlobalTheory.PolFan.balForms bar X →
      (∀ y, 0 ≤ f y y) → ∀ x, f x x = 0 → ∀ y, f x y = 0 := by
    intro f hf hfp x hx y
    have hsym : f y x = f x y := ((mem_bal f).1 hf).1 y x
    by_contra hne
    have expand : ∀ n : ℤ, f (n • x + y) (n • x + y) =
        n * n * f x x + n * f x y + n * f y x + f y y := by
      intro n
      simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    have key := hfp ((-(f y y + 1) * f x y) • x + y)
    rw [expand, hx, hsym] at key
    have h1 : 0 < f x y * f x y := mul_self_pos.2 hne
    have h2 : 1 ≤ f x y * f x y := by simpa using Int.add_one_le_iff.2 h1
    have h0 := hfp y
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ f y y + 1) (by linarith : (0:ℤ) ≤ f x y * f x y - 1)]
  obtain ⟨c, hc0, hcsum⟩ := hcone
  have hval : ∀ x y, ((β x y : ℤ) : ℝ) = ∑ i, c i * ((γ i x y : ℤ) : ℝ) := by
    intro x y
    have := congrArg (fun L : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => L x y) hcsum
    simpa [GlobalTheory.PolFan.toReal] using this
  set K : Submodule O X := GlobalTheory.PolFan.CarDim.orad β with hK
  have hKβ : ∀ x ∈ K, β x x = 0 := by
    intro x hx
    have := (GlobalTheory.PolFan.CarDim.mem_orad (O := O)).1 hx 1 x
    simpa using this
  let P : Fin m → Prop := fun j => ∀ x ∈ K, ∀ y, γ j x y = 0
  have hpos : ∀ j, 0 < c j → P j := by
    intro j hcj x hx
    apply psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x
    have hsum : ∑ i, c i * ((γ i x x : ℤ) : ℝ) = 0 := by
      rw [← hval, hKβ x hx]
      simp
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ c i * ((γ i x x : ℤ) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hcell.nonneg i x)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h hcj.ne'
    · exact_mod_cast h
  have hw : ∀ j, ∃ x ∈ K, (¬ P j → 0 < γ j x x) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, K.zero_mem, fun h => absurd hj h⟩
    · simp only [P, not_forall] at hj
      obtain ⟨x, hx, y, hxy⟩ := hj
      refine ⟨x, hx, fun _ => ?_⟩
      rcases (hcell.nonneg j x).lt_or_eq with h | h
      · exact h
      · exact absurd (psd_zero (γ j) (hcell.mem j) (hcell.nonneg j) x h.symm y) hxy
  choose w hwK hwpos using hw
  let h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ :=
    { toFun := fun f => ∑ j, f (w j) (w j)
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun a f => by simp [Finset.mul_sum] }
  have hh : ∀ f, h f = ∑ j, f (w j) (w j) := fun _ => rfl
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsT : ∀ j, j ∈ Set.range s ↔ P j := by
    intro j
    have hr : Set.range s = (T : Set (Fin m)) := Finset.range_orderEmbOfFin T rfl
    rw [hr]
    simp [T]
  have hPs : ∀ i, P (s i) := fun i => (hsT (s i)).1 ⟨i, rfl⟩
  have hfc : GlobalTheory.PolFan.IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [hh]
      exact Finset.sum_nonneg fun i _ => hcell.nonneg j (w i)
    · rw [hsT, hh]
      constructor
      · intro h0
        by_contra hj
        have hnn : ∀ i ∈ Finset.univ, 0 ≤ γ j (w i) (w i) := fun i _ => hcell.nonneg j (w i)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
        exact (hwpos j hj).ne' this
      · intro hj
        exact Finset.sum_eq_zero fun i _ => hj (w i) (hwK i) (w i)
  have hcell' := hface m T.card γ s h hcell hfc
  have hvanl : ∀ i, ∀ x ∈ K, ∀ y, γ (s i) x y = 0 := fun i => hPs i
  have hvanr : ∀ i, ∀ x y, y ∈ K → γ (s i) x y = 0 := by
    intro i x y hy
    rw [((mem_bal _).1 (hcell.mem (s i))).1 x y]
    exact hPs i y hy x
  choose δ hδ using fun i =>
    GlobalTheory.PolFan.CarDim.exists_pull_mkQ_eq_of_vanish K (γ (s i)) (hvanl i) (hvanr i)
  have hr : Function.Surjective K.mkQ := K.mkQ_surjective
  have hδap : ∀ i x y, δ i (K.mkQ x) (K.mkQ y) = γ (s i) x y := by
    intro i x y
    rw [← hδ i]
    rfl
  have heZ : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K),
      ψ.evalZ (GlobalTheory.PolFan.pull K.mkQ f) = ψ.evalZ f := by
    intro f
    exact ψ.eval_comp hr (fun a b => ((f a b : ℤ) : ℝ))
  have hpullbal : ∀ f ∈ GlobalTheory.PolFan.balForms bar (X ⧸ K),
      GlobalTheory.PolFan.pull K.mkQ f ∈ GlobalTheory.PolFan.balForms bar X := by
    intro f hf
    obtain ⟨hs, hb⟩ := (mem_bal f).1 hf
    refine (mem_bal _).2 ⟨fun y z => hs (K.mkQ y) (K.mkQ z), fun a y z => ?_⟩
    show f (K.mkQ (a • y)) (K.mkQ z) = f (K.mkQ y) (K.mkQ (bar a • z))
    rw [LinearMap.map_smul, LinearMap.map_smul]
    exact hb a (K.mkQ y) (K.mkQ z)
  have hpullpsd : ∀ f : LinearMap.BilinForm ℤ (X ⧸ K), (∀ q, 0 ≤ f q q) →
      ∀ y, 0 ≤ GlobalTheory.PolFan.pull K.mkQ f y y :=
    fun f hf y => hf (K.mkQ y)
  have hfun : (fun i => GlobalTheory.PolFan.pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  refine ⟨T.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i q => ?_, ?_, ?_⟩
    · refine (mem_bal _).2 ⟨fun a b => ?_, fun a u v => ?_⟩
      · obtain ⟨x, rfl⟩ := hr a
        obtain ⟨y, rfl⟩ := hr b
        rw [hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).1 x y
      · obtain ⟨x, rfl⟩ := hr u
        obtain ⟨y, rfl⟩ := hr v
        rw [← LinearMap.map_smul, ← LinearMap.map_smul, hδap, hδap]
        exact ((mem_bal _).1 (hcell.mem (s i))).2 a x y
    · obtain ⟨y, rfl⟩ := hr q
      rw [hδap]
      exact hcell.nonneg (s i) y
    · intro c hc
      have key := hcell'.linear.eval_eq_sum (X₁ := X ⧸ K) hr
        (B := fun a b => ∑ i, c i * ((δ i a b : ℤ) : ℝ)) hc (fun a b => by simp only [hδap])
      rw [key]
      refine Finset.sum_congr rfl fun i _ => ?_
      show c i * ψ.evalZ (γ (s i)) = c i * ψ.evalZ (δ i)
      rw [← hδ i, heZ]
    · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hcell'.strict
      refine ⟨N, ℓ.comp (GlobalTheory.PolFan.CarDim.pullLin K.mkQ), hN, fun i => ?_,
        fun β' hb hp => ?_, fun β' hb hp heq => ?_⟩
      · have h1i : ((ℓ (γ (s i)) : ℤ) : ℝ) = (N : ℝ) * ψ.evalZ (γ (s i)) := h1 i
        rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, hδ i, h1i, ← hδ i, heZ]
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ]
        exact h2 _ (hpullbal β' hb) (hpullpsd β' hp)
      · rw [LinearMap.comp_apply, GlobalTheory.PolFan.CarDim.pullLin_apply, ← heZ] at heq
        obtain ⟨k, c', hk, hkc⟩ := h3 _ (hpullbal β' hb) (hpullpsd β' hp) heq
        refine ⟨k, c', hk, ?_⟩
        have hkc' : k • GlobalTheory.PolFan.pull K.mkQ β' = ∑ i, c' i • γ (s i) := hkc
        apply GlobalTheory.PolFan.CarDim.pullLin_injective hr
        simp only [map_nsmul, map_zsmul, LinearMap.map_smul_of_tower, map_sum,
          GlobalTheory.PolFan.CarDim.pullLin_apply]
        rw [hkc']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ i]
  · rw [hfun]
    simp only [GlobalTheory.PolFan.InRCone]
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hcsum]
    have hmap : Finset.univ.map s = T := Finset.map_orderEmbOfFin_univ T rfl
    have e1 : (∑ i, c (s i) • GlobalTheory.PolFan.toReal (γ (s i))) =
        ∑ j ∈ T, c j • GlobalTheory.PolFan.toReal (γ j) := by
      exact (Finset.sum_map Finset.univ s (fun j => c j • GlobalTheory.PolFan.toReal (γ j))).symm.trans
        (by rw [hmap])
    rw [e1]
    symm
    apply Finset.sum_filter_of_ne
    intro j _ hne
    by_contra hj
    apply hne
    have hcj : c j = 0 := by
      rcases (hc0 j).lt_or_eq with h' | h'
      · exact absurd (hpos j h') hj
      · exact h'.symm
    rw [hcj, zero_smul]
  · rw [← GlobalTheory.PolFan.CarDim.genRank_pull hr δ, hfun]
    unfold GlobalTheory.PolFan.genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono
      (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.CompanionTheory.Ar.Fan.QuotientCellRadical
