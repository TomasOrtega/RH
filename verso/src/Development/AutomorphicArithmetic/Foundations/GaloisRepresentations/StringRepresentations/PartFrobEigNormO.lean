import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedFrobeniusEigenUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PartUnitary

/- English proof (translation)
Introduce `D ht hT i P Pa hB p hp w hu α hα`. Establish `hW` using `GlobalTheory.LocalInv.weightRegular_of_ext D.nd D.naut D.nbc`. Establish `hAut` using `ht.2.1`. Take `⟨ha1, hd1, hcsd⟩` from `hB.1 p hp`. Establish `hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ D.naut.infWt i τ`.

Introduce `τ`. Rewrite using `[← hB.2.2.2.2.2 τ]`. Unfold `isoInf`. Use `le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))` and prove the remaining obligations. Use `List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem (f := fun k : ℂ => (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)` and prove the remaining obligations.

Rewrite using `[GlobalTheory.LocalInv.list_coe]`. Conclude with `List.mem_map_of_mem (List.mem_range.mpr hd1)`. Establish `hnd : ∀ τ, (D.naut.infG p.π τ).Nodup` using `fun τ => Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW i P τ).1)`. Establish `hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2`. Introduce `τ z hz`.

Take `⟨k, hk⟩` from `(hW i P τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))`. Conclude with `⟨k, by rw [← hk]; push_cast; ring⟩`. Break down `Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩` into its components or cases. Establish `hr : D.naut.ralg p.π` using `(D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by`. Take `⟨k, hk⟩` from `hint τ z hz`.

Use `⟨k + m, ?_⟩` and prove the remaining obligations. Establish `hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m`. Conclude with `hm` after adjusting the coercions. Move the coercions through the operations in `at hm' ⊢`. Take the linear combination `hk + (1 / 2 : ℂ) * hm'⟩`.

Conclude with `(UpperTheory.GalN.tempo hT p.a p.π ha1 hcsd hr w).part hu α hα`. Establish `hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT)` using `(D.naut.ralg_def _).2 fun τ => by`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by`. Break down `(hAut.2.1 τ).1 with h | h` into its components or cases. Conclude with `⟨1 / 2, h, 0, by simp⟩`.

Conclude with `⟨-(1 / 2), h, -1, by push_cast; ring⟩`. Rewrite using `[D.naut.infG_tw _ _ τ s hs]`. Use `⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.mp hz`. Take `⟨k, hk⟩` from `hint τ y hy`.

Use `⟨k + k0 + m + 1, ?_⟩` and prove the remaining obligations. Establish `hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1`. Conclude with `hm` after adjusting the coercions. Move the coercions through the operations in `at hm' ⊢`. Rewrite using `[hk0]`.

Take the linear combination `hk + (1 / 2 : ℂ) * hm'`. Conclude with `(UpperTheory.GalN.tempo hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα`.
-/
theorem part_frobEig_norm_o : ∀ (D : D7), SumRepresentations.tie0 D → SumRepresentations.adm7 D → ∀ (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∀ p ∈ Pa, ∀ w : PlE D.host,
    D.naut.unr (D.naut.locG p.π w) → ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) α ∧ (p.a = 1 → ‖α‖ = 1) := by
  intro D ht hT i P Pa hB p hp w hu α hα
  have hW := GlobalTheory.LocalInv.weightRegular_of_ext D.nd D.naut D.nbc
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤
      D.naut.infWt i τ := by
    intro τ
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [GlobalTheory.LocalInv.list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd1)
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW i P τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (UpperTheory.GalN.tempo hT p.a p.π ha1 hcsd hr w).part hu α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    exact (UpperTheory.GalN.tempo hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα

end GlobalTheory.PartUnitary
