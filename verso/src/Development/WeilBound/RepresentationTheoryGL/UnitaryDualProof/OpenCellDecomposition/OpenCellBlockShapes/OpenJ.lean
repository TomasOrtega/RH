import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetMapSurjectiveWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolumeStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace PositivityTheory.RgUd.CellB

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ`. Take `⟨J, vol, hU, hL, hV⟩` from `GlobalTheory.T.open_cell_jacquet_integral_volume k ψ hψ h N d hd ρ hρ`. Take `⟨hfac, -⟩` from `GlobalTheory.T.unipotent_radical_decomposition_normal k h N d hd`. Take `⟨hl1, hl2⟩` from `GlobalTheory.T.open_cell_levi_unipotent_conjugation k ψ h N d hd`. Take `⟨-, huniq, -⟩` from `GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd`.

Establish `hUB : unipU k d hd ≤ unipB k (Fin N)` using `inf_le_left`. Establish `hLB : unipL k d hd ≤ unipB k (Fin N)` using `inf_le_left`. Establish `surj : Function.Surjective J`. Introduce `v`. Take `⟨L₀, hL₀U, hc, hO, hθ, f, hf, h1, h2⟩` from `GlobalTheory.T.exists_bump_section_on_compact_unipotent k ψ hψ h N d hd ρ hρ v`.

Take `⟨hpos, hJ⟩` from `hV L₀ hL₀U hc hO`. Establish `e` using `hJ ⟨f, hf⟩ v (fun u hb hu => by show f.1.1 (pm k (wOpen d hd) * u) = _`. Rewrite using `[h1 u hu, hθ u hb hu]`. Use the proof step `simp) h2`. Use `⟨((vol L₀ : ℂ))⁻¹ • ⟨f, hf⟩, ?_⟩` and prove the remaining obligations.

Establish `hne : (vol L₀ : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Rewrite using `[map_smul, e, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Establish `gen : ∀ (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (g : openFns d hd ρ), ∃ hx : parInd (stdBlocks d hd) ρ n g.1 - ((whitChar ψ N ⟨n, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ, J ⟨_, hx⟩ ∈ twKer ρ (unipM k d) (whitM d ψ)`. Introduce `n hn g`. Take `⟨a, ha, u, hu, rfl⟩` from `hfac n hn`.

Establish `hub` using `hUB hu`. Establish `hab` using `hLB ha`. Take `⟨m, hm, hθm⟩` from `hl1 a ha hab`. Set `g1 : openFns d hd ρ` to `⟨parInd (stdBlocks d hd) ρ u g.1, OpenCoinv.translate_mem d hd ρ hub g.2⟩`. Set `g2 : openFns d hd ρ` to `⟨parInd (stdBlocks d hd) ρ a g1.1, OpenCoinv.translate_mem d hd ρ hab g1.2⟩`.

Establish `e1 : J g1 = ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • J g` using `hU u hu hub g g1 rfl`. Establish `e2 : J g2 = ρ m.1 (J g1)` using `hL a ha m hm g1 g2 rfl`. Establish `e3 : parInd (stdBlocks d hd) ρ (a * u) g.1 = g2.1`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.

Establish `hθ : whitChar ψ N ⟨a * u, hn⟩ = whitChar ψ N ⟨a, hab⟩ * whitChar ψ N ⟨u, hub⟩`. Rewrite using `[← map_mul]`. Both sides reduce to the same expression. Establish `hx : parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ` using `sub_mem (OpenCoinv.translate_mem d hd ρ hn g.2) (Submodule.smul_mem _ _ g.2)`. Use `⟨hx, ?_⟩` and prove the remaining obligations.

Establish `e4 : (⟨_, hx⟩ : openFns d hd ρ) = g2 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g` using `Subtype.ext (by show parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 = g2.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1`. Rewrite using `[e3])`. Rewrite using `[e4, map_sub, map_smul, e2, e1, map_smul, hθ, hθm, Units.val_mul]`. Establish `e5 : ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • ρ m.1 (J g) - (((whitM d ψ m : ℂˣ) : ℂ) * ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ)) • J g = ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • (ρ m.1 (J g) - ((whitM d ψ m : ℂˣ) : ℂ) • J g)`. Rewrite using `[smul_sub, smul_smul, mul_comm]`.

Rewrite using `[e5]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, J g, rfl⟩)`. Establish `bwd : ∀ f : openFns d hd ρ, f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) → J f ∈ twKer ρ (unipM k d) (whitM d ψ)`. Introduce `f hf`. Establish `hs` using `GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ (unipB k (Fin N)) le_rfl (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) (whitChar ψ N) (fun q hq => rfl) f.1 f.2 hf`.

Take `⟨_, h2⟩` from `OpenCoinv.span_mem d hd ρ J (twKer ρ (unipM k d) (whitM d ψ)) _ (by`. Introduce and unpack `_ ⟨q, g, hg, rfl⟩`. Conclude with `gen q.1 q.2 ⟨g, hg⟩) hs`. Conclude with `h2`. Establish `key : ∀ f : openFns d hd ρ, J f = 0 → f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N)`.

Introduce `f hf`. Take `⟨L, hLU, hLc, hLO, hsupp⟩` from `GlobalTheory.T.open_cell_function_compact_support_unipotent k h N d hd ρ hρ f.1 f.2`. Establish `hLB' : L ≤ unipB k (Fin N)` using `hLU.trans hUB`. Set `θL : L →* ℂˣ` to `(whitChar ψ N).comp (Subgroup.inclusion hLB')`. Establish `hopen : IsOpen (θL.ker : Set L)` using `(GlobalTheory.Whittaker.isSmoothChar_whitChar (N := N) hψ).preimage (f := Subgroup.inclusion hLB') (continuous_subtype_val.subtype_mk fun x => hLB' x.2)`.

Take `⟨f', hd1, hd2, hd3⟩` from `GlobalTheory.T.projection_to_twisted_eigenfunction_support _ _ L hLc θL hopen f.1`. Establish `hsupp' : ∀ g, f'.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u`. Introduce `g hg`. Take `⟨l, hl, hne⟩` from `hd2 g hg`. Take `⟨p, hp, u, hu, e⟩` from `hsupp _ hne`.

Use `⟨p, hp, u * l⁻¹, mul_mem hu (inv_mem hl), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← e]`. Use `group`. Establish `hf'o : f' ∈ openFns d hd ρ` using `fun g hg => by`. Take `⟨p, hp, u, hu, e⟩` from `hsupp' g hg`.

Conclude with `⟨p, hp, u, hLB' hu, e⟩`. Establish `hdiff` using `GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ L hLB' (fun s hs => ⟨L, le_rfl, hs, hLc⟩) θL (fun q hq => rfl) (f.1 - f') (sub_mem f.2 hf'o) hd1`. Take `⟨hx, hJ0⟩` from `OpenCoinv.span_mem d hd ρ J ⊥ _ (by`. Introduce and unpack `_ ⟨q, g, hg, rfl⟩`. Establish `hqb` using `hLB' q.2`.

Establish `hx : parInd (stdBlocks d hd) ρ q.1 g - ((θL q : ℂˣ) : ℂ) • g ∈ openFns d hd ρ` using `sub_mem (OpenCoinv.translate_mem d hd ρ hqb hg) (Submodule.smul_mem _ _ hg)`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Set `g1 : openFns d hd ρ` to `⟨parInd (stdBlocks d hd) ρ q.1 g, OpenCoinv.translate_mem d hd ρ hqb hg⟩`. Establish `e1 : J g1 = ((whitChar ψ N ⟨q.1, hqb⟩ : ℂˣ) : ℂ) • J ⟨g, hg⟩` using `hU q.1 (hLU q.2) hqb ⟨g, hg⟩ g1 rfl`. Establish `e2 : (⟨_, hx⟩ : openFns d hd ρ) = g1 - ((θL q : ℂˣ) : ℂ) • ⟨g, hg⟩` using `rfl`.

Rewrite using `[e2, map_sub, map_smul, e1]`. Conclude with `(sub_self _ : _ = (0 : W))) hdiff`. Set `F' : openFns d hd ρ` to `⟨f', hf'o⟩`. Establish `hJF : J F' = 0`. Establish `e : (⟨_, hx⟩ : openFns d hd ρ) = f - F'` using `rfl`.

Rewrite `hJ0` using `[e, map_sub, hf]`. Simplify using `using hJ0`. Take `⟨hpos, hJ⟩` from `hV L hLU hLc hLO`. Establish `hv` using `hJ F' (f'.1.1 (pm k (wOpen d hd))) (fun u hb hu => hd3 ⟨u, hu⟩ _) (fun u hu hnot => by`. Assume the negation of the conclusion as `hne`.

Take `⟨p, hp, l, hl, e⟩` from `hsupp' _ hne`. Conclude with `hnot (huniq p hp l (hLU hl) u hu e.symm ▸ hl))`. Establish `hne : (vol L : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Establish `hv0 : f'.1.1 (pm k (wOpen d hd)) = 0`. Rewrite `hv` using `[hJF]`.

Conclude with `(smul_eq_zero.1 hv.symm).resolve_left hne`. Establish `hf0 : f' = 0`. Use `Subtype.ext (Subtype.ext (funext fun g => ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hg`. Take `⟨p, hp, l, hl, e⟩` from `hsupp' g hg`.

Apply `hg` to reduce the goal to its premises. Establish `h1` using `f'.1.2 ⟨p, hp⟩ (pm k (wOpen d hd))`. Rewrite `h1` using `[hv0, map_zero]`. Rewrite using `[e]`. Establish `h2` using `hd3 ⟨l, hl⟩ (p * pm k (wOpen d hd))`.

Rewrite `h2` using `[show f'.1.1 (p * pm k (wOpen d hd)) = 0 from h1, smul_zero]`. Conclude with `h2`. Rewrite `hd1` using `[hf0, sub_zero]`. Use `(Submodule.span_le.2 ?_ : twKer (parInd (stdBlocks d hd) ρ) L θL ≤ _) hd1` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`.

Conclude with `Submodule.subset_span ⟨⟨n.1, hLB' n.2⟩, v, rfl⟩`. Establish `lift : ∀ s ∈ twKer ρ (unipM k d) (whitM d ψ), ∃ F : openFns d hd ρ, F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s`. Introduce `s hs`. Use `Submodule.span_induction (p := fun s _ => ∃ F : openFns d hd ρ, F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s) ?_ ?_ ?_ ?_ hs` and prove the remaining obligations. Introduce and unpack `_ ⟨m, v, rfl⟩`.

Take `⟨g, rfl⟩` from `surj v`. Take `⟨a, ha, hm⟩` from `hl2 m`. Establish `hab` using `hLB ha`. Take `⟨m', hm', hθ⟩` from `hl1 a ha hab`. Establish `hmm : m = m'` using `Subtype.ext (OpenCoinv.leviEmb_inj d hd (hm.symm.trans hm'))`.

Substitute `hmm` using the available equality. Set `g1 : openFns d hd ρ` to `⟨parInd (stdBlocks d hd) ρ a g.1, OpenCoinv.translate_mem d hd ρ hab g.2⟩`. Use `⟨g1 - ((whitChar ψ N ⟨a, hab⟩ : ℂˣ) : ℂ) • g, Submodule.subset_span ⟨⟨a, hab⟩, g.1, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, hL a ha m hm g g1 rfl, hθ]`. Conclude with `⟨0, zero_mem _, map_zero J⟩`.

Introduce and unpack `x y _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩`. Conclude with `⟨F + F', add_mem hF hF', map_add J F F'⟩`. Introduce and unpack `c x _ ⟨F, hF, rfl⟩`. Conclude with `⟨c • F, Submodule.smul_mem _ c hF, map_smul J c F⟩`. Use `⟨J, vol, surj, fun f => ⟨fun hf => ?_, bwd f⟩, hU, hL, hV⟩` and prove the remaining obligations.

Take `⟨F, hF, e⟩` from `lift _ hf`. Establish `h0` using `key (f - F) (by rw [map_sub, e, sub_self])`. Establish `h1 : (f : IndSp (stdBlocks d hd) ρ) = (f - F).1 + F.1` using `by show (f : IndSp (stdBlocks d hd) ρ) = (f.1 - F.1) + F.1`. Rewrite using `[sub_add_cancel]`. Rewrite using `[h1]`.

Conclude with `add_mem h0 hF`.
-/
theorem openJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ →
    ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), Function.Surjective J ∧
      (∀ f : openFns d hd ρ, J f ∈ twKer ρ (unipM k d) (whitM d ψ) ↔
        (f : IndSp (stdBlocks d hd) ρ) ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N)) ∧
      (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ),
        (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧
      (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d),
        pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 →
        ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧
      ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) →
        (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) →
        0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
          (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ →
            f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
          (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  obtain ⟨J, vol, hU, hL, hV⟩ := GlobalTheory.T.open_cell_jacquet_integral_volume k ψ hψ h N d hd ρ hρ
  obtain ⟨hfac, -⟩ := GlobalTheory.T.unipotent_radical_decomposition_normal k h N d hd
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.open_cell_levi_unipotent_conjugation k ψ h N d hd
  obtain ⟨-, huniq, -⟩ := GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd
  have hUB : unipU k d hd ≤ unipB k (Fin N) := inf_le_left
  have hLB : unipL k d hd ≤ unipB k (Fin N) := inf_le_left
  have surj : Function.Surjective J := by
    intro v
    obtain ⟨L₀, hL₀U, hc, hO, hθ, f, hf, h1, h2⟩ := GlobalTheory.T.exists_bump_section_on_compact_unipotent k ψ hψ h N d hd ρ hρ v
    obtain ⟨hpos, hJ⟩ := hV L₀ hL₀U hc hO
    have e := hJ ⟨f, hf⟩ v (fun u hb hu => by
      show f.1.1 (pm k (wOpen d hd) * u) = _
      rw [h1 u hu, hθ u hb hu]
      simp) h2
    refine ⟨((vol L₀ : ℂ))⁻¹ • ⟨f, hf⟩, ?_⟩
    have hne : (vol L₀ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have gen : ∀ (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (g : openFns d hd ρ),
      ∃ hx : parInd (stdBlocks d hd) ρ n g.1 - ((whitChar ψ N ⟨n, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ,
        J ⟨_, hx⟩ ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro n hn g
    obtain ⟨a, ha, u, hu, rfl⟩ := hfac n hn
    have hub := hUB hu
    have hab := hLB ha
    obtain ⟨m, hm, hθm⟩ := hl1 a ha hab
    let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ u g.1, OpenCoinv.translate_mem d hd ρ hub g.2⟩
    let g2 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g1.1, OpenCoinv.translate_mem d hd ρ hab g1.2⟩
    have e1 : J g1 = ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • J g := hU u hu hub g g1 rfl
    have e2 : J g2 = ρ m.1 (J g1) := hL a ha m hm g1 g2 rfl
    have e3 : parInd (stdBlocks d hd) ρ (a * u) g.1 = g2.1 := by
      rw [map_mul]
      rfl
    have hθ : whitChar ψ N ⟨a * u, hn⟩ = whitChar ψ N ⟨a, hab⟩ * whitChar ψ N ⟨u, hub⟩ := by
      rw [← map_mul]
      rfl
    have hx : parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ :=
      sub_mem (OpenCoinv.translate_mem d hd ρ hn g.2) (Submodule.smul_mem _ _ g.2)
    refine ⟨hx, ?_⟩
    have e4 : (⟨_, hx⟩ : openFns d hd ρ) = g2 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g :=
      Subtype.ext (by
        show parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 =
          g2.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1
        rw [e3])
    rw [e4, map_sub, map_smul, e2, e1, map_smul, hθ, hθm, Units.val_mul]
    have e5 : ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • ρ m.1 (J g) -
        (((whitM d ψ m : ℂˣ) : ℂ) * ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ)) • J g =
        ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • (ρ m.1 (J g) - ((whitM d ψ m : ℂˣ) : ℂ) • J g) := by
      rw [smul_sub, smul_smul, mul_comm]
    rw [e5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, J g, rfl⟩)
  have bwd : ∀ f : openFns d hd ρ, f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) →
      J f ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro f hf
    have hs := GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ (unipB k (Fin N)) le_rfl
      (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) (whitChar ψ N)
      (fun q hq => rfl) f.1 f.2 hf
    obtain ⟨_, h2⟩ := OpenCoinv.span_mem d hd ρ J (twKer ρ (unipM k d) (whitM d ψ)) _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      exact gen q.1 q.2 ⟨g, hg⟩) hs
    exact h2
  have key : ∀ f : openFns d hd ρ, J f = 0 →
      f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
    intro f hf
    obtain ⟨L, hLU, hLc, hLO, hsupp⟩ := GlobalTheory.T.open_cell_function_compact_support_unipotent k h N d hd ρ hρ f.1 f.2
    have hLB' : L ≤ unipB k (Fin N) := hLU.trans hUB
    let θL : L →* ℂˣ := (whitChar ψ N).comp (Subgroup.inclusion hLB')
    have hopen : IsOpen (θL.ker : Set L) :=
      (GlobalTheory.Whittaker.isSmoothChar_whitChar (N := N) hψ).preimage (f := Subgroup.inclusion hLB') (continuous_subtype_val.subtype_mk fun x => hLB' x.2)
    obtain ⟨f', hd1, hd2, hd3⟩ := GlobalTheory.T.projection_to_twisted_eigenfunction_support _ _ L hLc θL hopen f.1
    have hsupp' : ∀ g, f'.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
      intro g hg
      obtain ⟨l, hl, hne⟩ := hd2 g hg
      obtain ⟨p, hp, u, hu, e⟩ := hsupp _ hne
      refine ⟨p, hp, u * l⁻¹, mul_mem hu (inv_mem hl), ?_⟩
      rw [← mul_assoc, ← e]
      group
    have hf'o : f' ∈ openFns d hd ρ := fun g hg => by
      obtain ⟨p, hp, u, hu, e⟩ := hsupp' g hg
      exact ⟨p, hp, u, hLB' hu, e⟩
    have hdiff := GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ L hLB' (fun s hs => ⟨L, le_rfl, hs, hLc⟩) θL
      (fun q hq => rfl) (f.1 - f') (sub_mem f.2 hf'o) hd1
    obtain ⟨hx, hJ0⟩ := OpenCoinv.span_mem d hd ρ J ⊥ _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      have hqb := hLB' q.2
      have hx : parInd (stdBlocks d hd) ρ q.1 g - ((θL q : ℂˣ) : ℂ) • g ∈ openFns d hd ρ :=
        sub_mem (OpenCoinv.translate_mem d hd ρ hqb hg) (Submodule.smul_mem _ _ hg)
      refine ⟨hx, ?_⟩
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ q.1 g, OpenCoinv.translate_mem d hd ρ hqb hg⟩
      have e1 : J g1 = ((whitChar ψ N ⟨q.1, hqb⟩ : ℂˣ) : ℂ) • J ⟨g, hg⟩ := hU q.1 (hLU q.2) hqb ⟨g, hg⟩ g1 rfl
      have e2 : (⟨_, hx⟩ : openFns d hd ρ) = g1 - ((θL q : ℂˣ) : ℂ) • ⟨g, hg⟩ := rfl
      rw [e2, map_sub, map_smul, e1]
      exact (sub_self _ : _ = (0 : W))) hdiff
    let F' : openFns d hd ρ := ⟨f', hf'o⟩
    have hJF : J F' = 0 := by
      have e : (⟨_, hx⟩ : openFns d hd ρ) = f - F' := rfl
      rw [e, map_sub, hf] at hJ0
      simpa using hJ0
    obtain ⟨hpos, hJ⟩ := hV L hLU hLc hLO
    have hv := hJ F' (f'.1.1 (pm k (wOpen d hd))) (fun u hb hu => hd3 ⟨u, hu⟩ _) (fun u hu hnot => by
      by_contra hne
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' _ hne
      exact hnot (huniq p hp l (hLU hl) u hu e.symm ▸ hl))
    have hne : (vol L : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hv0 : f'.1.1 (pm k (wOpen d hd)) = 0 := by
      rw [hJF] at hv
      exact (smul_eq_zero.1 hv.symm).resolve_left hne
    have hf0 : f' = 0 := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      by_contra hg
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' g hg
      apply hg
      have h1 := f'.1.2 ⟨p, hp⟩ (pm k (wOpen d hd))
      rw [hv0, map_zero] at h1
      rw [e]
      have h2 := hd3 ⟨l, hl⟩ (p * pm k (wOpen d hd))
      rw [show f'.1.1 (p * pm k (wOpen d hd)) = 0 from h1, smul_zero] at h2
      exact h2
    rw [hf0, sub_zero] at hd1
    refine (Submodule.span_le.2 ?_ : twKer (parInd (stdBlocks d hd) ρ) L θL ≤ _) hd1
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨⟨n.1, hLB' n.2⟩, v, rfl⟩
  have lift : ∀ s ∈ twKer ρ (unipM k d) (whitM d ψ), ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨m, v, rfl⟩
      obtain ⟨g, rfl⟩ := surj v
      obtain ⟨a, ha, hm⟩ := hl2 m
      have hab := hLB ha
      obtain ⟨m', hm', hθ⟩ := hl1 a ha hab
      have hmm : m = m' := Subtype.ext (OpenCoinv.leviEmb_inj d hd (hm.symm.trans hm'))
      subst hmm
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g.1, OpenCoinv.translate_mem d hd ρ hab g.2⟩
      refine ⟨g1 - ((whitChar ψ N ⟨a, hab⟩ : ℂˣ) : ℂ) • g, Submodule.subset_span ⟨⟨a, hab⟩, g.1, rfl⟩, ?_⟩
      rw [map_sub, map_smul, hL a ha m hm g g1 rfl, hθ]
    · exact ⟨0, zero_mem _, map_zero J⟩
    · rintro x y _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩
      exact ⟨F + F', add_mem hF hF', map_add J F F'⟩
    · rintro c x _ ⟨F, hF, rfl⟩
      exact ⟨c • F, Submodule.smul_mem _ c hF, map_smul J c F⟩
  refine ⟨J, vol, surj, fun f => ⟨fun hf => ?_, bwd f⟩, hU, hL, hV⟩
  obtain ⟨F, hF, e⟩ := lift _ hf
  have h0 := key (f - F) (by rw [map_sub, e, sub_self])
  have h1 : (f : IndSp (stdBlocks d hd) ρ) = (f - F).1 + F.1 := by
    show (f : IndSp (stdBlocks d hd) ρ) = (f.1 - F.1) + F.1
    rw [sub_add_cancel]
  rw [h1]
  exact add_mem h0 hF

end PositivityTheory.RgUd.CellB
