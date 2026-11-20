import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.PC

section LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

abbrev SV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

abbrev latA (Λ : Submodule (𝓞 E) (n → E)) : Submodule 𝒮 (n → 𝒜) := latS (F := F) 𝔸 𝒮 Λ

abbrev latV (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (SV E v) (n → E ⊗[F] v.adicCompletion F) := latS (F := F) (v.adicCompletion F) (SV E v) Λ

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero`.

Establish `: (fun i => prV (E` using `E) v ((0 : n → 𝒜) i)) = 0 := by ext i; simp`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`. Establish `: (fun i => prV (E` using `E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by ext i; simp`.

Rewrite using `[this]`. Conclude with `add_mem ha hb`. Consider the case `smul s a _ ha`. Establish `: (fun i => prV (E` using `E) v ((s • a) i)) = (⟨prV (E := E) v (s : 𝒜), afsplit_prV_int v _ s.2⟩ : SV E v) • (fun i => prV (E := E) v (a i)) := by`. Use extensionality with `i`.

Simplify using `only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem pr_lat (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) (y : n → 𝒜)
    (hy : y ∈ latA (F := F) Λ) : (fun i => prV (E := E) v (y i)) ∈ latV v Λ := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => prV (E := E) v ((a + b) i)) =
        (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v (s : 𝒜), afsplit_prV_int v _ s.2⟩ : SV E v) • (fun i => prV (E := E) v (a i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨x, hx, rfl⟩` from `hu`. Establish `: (fun i => afsplitIE v (inclE (F` using `F) (v.adicCompletion F) (x i))) = (⟨afsplitEps E v, afsplit_eps_int v⟩ : 𝒮) • (fun i => inclE (F := F) 𝔸 (x i)) := by`. Use extensionality with `i`.

Simplify using `only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]`. Rewrite using `[← afsplit_decomp, afsplit_prV_inclE]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)`. Consider the case `zero`.

Establish `: (fun i => afsplitIE v ((0 : n → E ⊗[F] v.adicCompletion F) i)) = 0` using `by ext i; simp`. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`. Establish `: (fun i => afsplitIE v ((a + b) i)) = (fun i => afsplitIE v (a i)) + (fun i => afsplitIE v (b i))` using `by ext i; simp`.

Rewrite using `[this]`. Conclude with `add_mem ha hb`. Consider the case `smul s a _ ha`. Establish `: (fun i => afsplitIE v ((s • a) i)) = (⟨afsplitIE v (s : E ⊗[F] v.adicCompletion F), afsplit_IE_int v _ s.2⟩ : 𝒮) • (fun i => afsplitIE v (a i))`. Use extensionality with `i`.

Simplify using `only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem ie_lat (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F) (hu : u ∈ latV v Λ) :
    (fun i => afsplitIE v (u i)) ∈ latA (F := F) Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have : (fun i => afsplitIE v (inclE (F := F) (v.adicCompletion F) (x i))) =
        (⟨afsplitEps E v, afsplit_eps_int v⟩ : 𝒮) • (fun i => inclE (F := F) 𝔸 (x i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      rw [← afsplit_decomp, afsplit_prV_inclE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero =>
    have : (fun i => afsplitIE v ((0 : n → E ⊗[F] v.adicCompletion F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => afsplitIE v ((a + b) i)) =
        (fun i => afsplitIE v (a i)) + (fun i => afsplitIE v (b i)) := by ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => afsplitIE v ((s • a) i)) =
        (⟨afsplitIE v (s : E ⊗[F] v.adicCompletion F), afsplit_IE_int v _ s.2⟩ : 𝒮) •
          (fun i => afsplitIE v (a i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha

/- English proof (translation)
Establish `hmem : ∀ w : HeightOneSpectrum (𝓞 F), (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0 else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) ∈ w.adicCompletionIntegers F`. Introduce `w`. Use `split_ifs with h`. Conclude with `zero_mem _`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]`.

Establish `h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) ≤ 1` using `levelaf_int_mem_v w D`. Establish `h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) = 1` using `le_antisymm h1 (not_lt.1 h)`. Rewrite using `[h2, inv_one]`. Set `u : 𝔸` to `⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0 else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹, Filter.Eventually.of_forall hmem⟩`. Use `⟨(levelaf_finite_places D hD).toFinset, u, hmem, ?_⟩` and prove the remaining obligations.

Use `FiniteAdeleRing.ext _ fun w => ?_` and prove the remaining obligations. Establish `hsum : (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) w = if w ∈ (levelaf_finite_places D hD).toFinset then 1 else 0`. Express the relevant statement in the definitionally equal form `evalV F w (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) = _`. Rewrite using `[map_sum]`. Use `split_ifs with h`.

Rewrite using `[Finset.sum_eq_single_of_mem w h]`. Conclude with `afsplitI_self w 1`. Introduce `b _ hb`. Conclude with `afsplitI_ne b w hb.symm 1`. Use `Finset.sum_eq_zero fun b hb => afsplitI_ne b w ?_ 1` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `h hb`. Rewrite using `[afsplit_add_apply, afsplit_mul_apply, hsum]`. Use `show (1 : w.adicCompletion F) = algebraMap (𝓞 F) (w.adicCompletion F) D * (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0 else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) + _`. Distinguish the cases in `h : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1`.

Establish `h' : w ∈ (levelaf_finite_places D hD).toFinset` using `by simpa using h`. Rewrite using `[if_pos h, if_pos h', mul_zero, zero_add]`. Establish `h' : w ∉ (levelaf_finite_places D hD).toFinset` using `by simpa using h`. Rewrite using `[if_neg h, if_neg h', add_zero, mul_inv_cancel₀ (levelaf_algebraMap_ne_zero w D hD)]`.
-/
theorem unit_away (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (u : 𝔸), u ∈ intAd F ∧
      (1 : 𝔸) = algebraMap (𝓞 F) 𝔸 D * u + ∑ v ∈ T, afsplitI v 1 := by
  classical
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F),
      (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) ∈ w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact zero_mem _
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) ≤ 1 := levelaf_int_mem_v w D
      have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) = 1 := le_antisymm h1 (not_lt.1 h)
      rw [h2, inv_one]
  let u : 𝔸 := ⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹, Filter.Eventually.of_forall hmem⟩
  refine ⟨(levelaf_finite_places D hD).toFinset, u, hmem, ?_⟩
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hsum : (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) w =
      if w ∈ (levelaf_finite_places D hD).toFinset then 1 else 0 := by
    change evalV F w (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) = _
    rw [map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single_of_mem w h]
      · exact afsplitI_self w 1
      · intro b _ hb; exact afsplitI_ne b w hb.symm 1
    · refine Finset.sum_eq_zero fun b hb => afsplitI_ne b w ?_ 1
      rintro rfl; exact h hb
  rw [afsplit_add_apply, afsplit_mul_apply, hsum]
  show (1 : w.adicCompletion F) = algebraMap (𝓞 F) (w.adicCompletion F) D *
    (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) + _
  by_cases h : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1
  · have h' : w ∈ (levelaf_finite_places D hD).toFinset := by simpa using h
    rw [if_pos h, if_pos h', mul_zero, zero_add]
  · have h' : w ∉ (levelaf_finite_places D hD).toFinset := by simpa using h
    rw [if_neg h, if_neg h', add_zero, mul_inv_cancel₀ (levelaf_algebraMap_ne_zero w D hD)]

end LG

end Formalism.L2.Geo.Def.PC
