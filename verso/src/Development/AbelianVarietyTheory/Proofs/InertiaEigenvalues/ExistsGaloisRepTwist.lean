import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepWeilJumpsStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HalfTwist

/- English proof (translation)
Introduce `W _`. Take `⟨W', hW'⟩` from `Submodule.exists_isCompl W`. Use `⟨W', fun g v hv => ?_, hW'⟩` and prove the remaining obligations. Establish `h : ((χ g : GL _ _) : Matrix (Fin 1) (Fin 1) k).mulVec v = ((χ g : GL _ _) : Matrix (Fin 1) (Fin 1) k) 0 0 • v`. Use function extensionality and compare the values at `j`.

Use `fin_cases j`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[h]`. Conclude with `W'.smul_mem _ hv`.
-/
theorem isSSRep_rank_one {Γ k : Type} [Group Γ] [Field k] (χ : Γ →* GL (Fin 1) k) : IsSSRep χ := by
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  refine ⟨W', fun g v hv => ?_, hW'⟩
  have h : ((χ g : GL _ _) : Matrix (Fin 1) (Fin 1) k).mulVec v =
      ((χ g : GL _ _) : Matrix (Fin 1) (Fin 1) k) 0 0 • v := by
    funext j
    fin_cases j
    simp [Matrix.mulVec, dotProduct]
  rw [h]
  exact W'.smul_mem _ hv

/- English proof (translation)
Establish `hu` using `D.naut.etaT_unr w`. Establish `hinv` using `D.naut.etaTinv_def w`. Establish `hd1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1` using `D.naut.locG_dim _ _`. Establish `hcard : Multiset.card (D.naut.frobEig (D.naut.locG D.naut.etaT w)) = 1`. Rewrite using `[D.naut.frobEig_card _ hu, D.naut.locG_dim]`.

Take `⟨b, hb⟩` from `Multiset.card_eq_one.1 hcard`. Establish `hb0 : b ≠ 0`. Establish `h0` using `D.naut.frobEig_ne_zero _ hu`. Rewrite `h0` using `[hb]`. Introduce `hb'`.

Conclude with `h0 (by simp [hb'])`. Establish `hinvb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {b⁻¹}`. Rewrite using `[hinv.2, hb, Multiset.map_singleton]`. Establish `hunr` using `D.naut.unr_char _ _ hd1 hu hinv.1`. Establish `hf` using `D.naut.frobEig_char _ _ b⁻¹ hu hinv.1 hd1 hinvb`.

Rewrite using `[D.naut.unr_eq_lpUnr _ hunr, hf, hb, Multiset.map_singleton, mul_inv_cancel₀ hb0]`.
-/
theorem eta_char (D : D7) (w : PlE D.host) :
    D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
  have hu := D.naut.etaT_unr w
  have hinv := D.naut.etaTinv_def w
  have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hcard : Multiset.card (D.naut.frobEig (D.naut.locG D.naut.etaT w)) = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    have h0 := D.naut.frobEig_ne_zero _ hu
    rw [hb] at h0
    intro hb'
    exact h0 (by simp [hb'])
  have hinvb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {b⁻¹} := by
    rw [hinv.2, hb, Multiset.map_singleton]
  have hunr := D.naut.unr_char _ _ hd1 hu hinv.1
  have hf := D.naut.frobEig_char _ _ b⁻¹ hu hinv.1 hd1 hinvb
  rw [D.naut.unr_eq_lpUnr _ hunr, hf, hb, Multiset.map_singleton, mul_inv_cancel₀ hb0]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hA.2.1 τ`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `⟨1 / 2, h1, by rw [h2, h1, Multiset.map_singleton], Or.inl rfl⟩`. Conclude with `⟨-(1 / 2), h1, by rw [h2, h1, Multiset.map_singleton], Or.inr rfl⟩`.
-/
theorem eta_inf (D : D7) (hA : SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) :
    ∃ h : ℂ, D.naut.infG D.naut.etaT τ = {h} ∧ D.naut.infG D.naut.etaTinv τ = {-h} ∧
      (h = 1 / 2 ∨ h = -(1 / 2)) := by
  obtain ⟨h1, h2⟩ := hA.2.1 τ
  rcases h1 with h1 | h1
  · exact ⟨1 / 2, h1, by rw [h2, h1, Multiset.map_singleton], Or.inl rfl⟩
  · exact ⟨-(1 / 2), h1, by rw [h2, h1, Multiset.map_singleton], Or.inr rfl⟩

end GlobalTheory.HalfTwist

open GlobalTheory.HalfTwist in

/- English proof (translation)
Introduce `D htie hadm i a ha π e hcsd hinf`. Take `⟨hLP, hAut, hGal⟩` from `htie`. Take `⟨hG1, -, hG3⟩` from `hadm i`. Establish `hoff : ∀ {b : ℕ} (ρ : GE D.nd →* GL (Fin b) (Qbar (D.nd.l i))) (f : ∀ w, D.naut.LP w), (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = f w) → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.wdOf i ρ w = f w) → ∀ w, D.naut.wdOf i ρ w = f w`. Introduce `b ρ f h1 h2 w`.

Distinguish the cases in `hw : w ∈ placesOver D.host.E (D.nd.l i)`. Conclude with `h2 w hw`. Conclude with `h1 w hw`. Break down `Int.even_or_odd (e + (a : ℤ) - 1) with ⟨k, hk⟩ | ⟨k, hk⟩` into its components or cases. Establish `hkC : (e : ℂ) + (a : ℂ) - 1 = (k : ℂ) + (k : ℂ)` using `by exact_mod_cast hk`.

Establish `hkR : (e : ℝ) + (a : ℝ) - 1 = (k : ℝ) + (k : ℝ)` using `by exact_mod_cast hk`. Establish `hralg : D.naut.ralg π`. Rewrite using `[D.naut.ralg_def]`. Introduce `τ`. Use `⟨(hinf τ).1, fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨m, hm⟩` from `(hinf τ).2 z hz`. Conclude with `⟨m - k, by push_cast; linear_combination hm - hkC / 2⟩`. Take `⟨ρ₀, hc0, hss0, hoff0, hon0⟩` from `hG1 a ha π hcsd hralg`. Establish `hinf0 : ∀ τ, D.naut.infG (D.naut.tw D.naut.etaT D.naut.etaTinv) τ = {0}`. Introduce `τ`.

Take `⟨h, h1, h2, -⟩` from `eta_inf D hAut τ`. Rewrite using `[D.naut.infG_tw _ _ τ (-h) h2, h1, Multiset.map_singleton, add_neg_cancel]`. Take `⟨ρχ, hcχ, hoffχ, honχ⟩` from `hG3 (D.naut.tw D.naut.etaT D.naut.etaTinv) (k : ℝ) (fun τ z hz => by`. Rewrite `hz` using `[hinf0, Multiset.mem_singleton]`. Conclude with `⟨k, by rw [hz]; push_cast; ring⟩)`.

Take `⟨ρ', h1, h2, h3, h4⟩` from `GlobalTheory.T.galois_rep_weil_jumps D ⟨hLP, hAut, hGal⟩ i a ρ₀ ρχ (fun w => D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (fun w => D.naut.lpTw (D.naut.locG (D.naut.tw D.naut.etaT D.naut.etaTinv) w) (k : ℝ)) (fun τ => (D.naut.infG π τ).map (fun z => -z + ((a : ℂ) - 1) / 2)) …`. Rewrite using `[(honχ w hw).2.2 τ hτ, hinf0, Multiset.map_singleton, zero_add]`. Use `push_cast`. Use the proof step `rfl⟩⟩`. Use `⟨ρ', h1, h2, fun w => ?_, fun w hw => ⟨(h4 w hw).1, fun τ hτ => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[h3 w]`. Establish `hU : D.naut.lpDim (D.naut.lpUnr w {1}) = 1`. Rewrite using `[(D.naut.lpUnr_spec w {1} (by simp)).2.2, Multiset.card_singleton]`. Rewrite using `[D.naut.locG_tw, eta_char, (hLP w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (D.naut.lpUnr w {1}) (D.naut.lpUnr w {1}) (k : ℝ) hU hU).2.2.1, (hLP w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (D.naut.lpTw (D.nau …`. Use `congr 1`.

Take the linear combination `(-1 / 2 : ℝ) * hkR`. Rewrite using `[(h4 w hw).2 τ hτ, Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Take the linear combination `hkC / 2`.

Establish `hkC : (e : ℂ) + (a : ℂ) - 1 = 2 * (k : ℂ) + 1` using `by exact_mod_cast hk`. Establish `hkR : (e : ℝ) + (a : ℝ) - 1 = 2 * (k : ℝ) + 1` using `by exact_mod_cast hk`. Establish `hcsd' : D.naut.csd (D.naut.tw π D.naut.etaT)` using `D.naut.csd_tw π D.naut.etaT hAut.1.1 hcsd`. Establish `hinfπ : ∀ τ, D.naut.infG (D.naut.tw π D.naut.etaT) τ = (D.naut.infG π τ).map (· + (D.naut.infG D.naut.etaT τ).sum)`. Introduce `τ`.

Take `⟨h, h1, -, -⟩` from `eta_inf D hAut τ`. Rewrite using `[D.naut.infG_tw π D.naut.etaT τ h h1, h1, Multiset.sum_singleton]`. Establish `hralg : D.naut.ralg (D.naut.tw π D.naut.etaT)`. Rewrite using `[D.naut.ralg_def]`. Introduce `τ`.

Take `⟨h, h1, -, hh⟩` from `eta_inf D hAut τ`. Rewrite using `[D.naut.infG_tw π D.naut.etaT τ h h1]`. Use `⟨(hinf τ).1.map (add_left_injective h), fun z' hz' => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, rfl⟩` from `Multiset.mem_map.1 hz'`. Take `⟨m, hm⟩` from `(hinf τ).2 z hz`.

Break down `hh with rfl | rfl` into its components or cases. Conclude with `⟨m - k, by push_cast; linear_combination hm - hkC / 2⟩`. Conclude with `⟨m - k - 1, by push_cast; linear_combination hm - hkC / 2⟩`. Take `⟨ρ₀, hc0, hss0, hoff0, hon0⟩` from `hG1 a ha _ hcsd' hralg`. Take `⟨ρχ, hcχ, hoffχ, honχ⟩` from `hG3 D.naut.etaTinv ((k : ℝ) + 1 / 2) (fun τ z hz => by`.

Take `⟨h, -, h2, hh⟩` from `eta_inf D hAut τ`. Rewrite `hz` using `[h2, Multiset.mem_singleton]`. Break down `hh with rfl | rfl` into its components or cases. Conclude with `⟨k, by rw [hz]; push_cast; ring⟩`. Conclude with `⟨k + 1, by rw [hz]; push_cast; ring⟩)`.

Take `⟨ρ', h1, h2, h3, h4⟩` from `GlobalTheory.T.galois_rep_weil_jumps D ⟨hLP, hAut, hGal⟩ i a ρ₀ ρχ (fun w => D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaT) w) ((1 - (a : ℝ)) / 2)) (fun w => D.naut.lpTw (D.naut.locG D.naut.etaTinv w) ((k : ℝ) + 1 / 2)) (fun τ => (D.naut.infG (D.naut.tw π D.naut.etaT) τ).map …`. Rewrite using `[(honχ w hw).2.2 τ hτ]`. Take `⟨h, -, h2, -⟩` from `eta_inf D hAut ((D.naut.iotaQC i).toRingHom.comp τ)`. Rewrite using `[h2, Multiset.map_singleton, Multiset.sum_singleton]⟩⟩`. Use `⟨ρ', h1, h2, fun w => ?_, fun w hw => ⟨(h4 w hw).1, fun τ hτ => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[h3 w]`. Establish `hU : D.naut.lpDim (D.naut.lpUnr w {1}) = 1`. Rewrite using `[(D.naut.lpUnr_spec w {1} (by simp)).2.2, Multiset.card_singleton]`. Establish `hη : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1` using `D.naut.locG_dim _ _`. Establish `hη' : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1` using `D.naut.locG_dim _ _`.

Rewrite using `[D.naut.locG_tw, (hLP w (D.naut.lpTw (D.naut.lpChar (D.naut.locG π w) (D.naut.locG D.naut.etaT w)) ((1 - (a : ℝ)) / 2)) (D.naut.locG π w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) ((k : ℝ) + 1 / 2) hη' hη').2.2.1, (hLP w (D.naut.lpChar (D.naut.locG π w) (D.nau …`. Use `congr 1`. Take the linear combination `(-1 / 2 : ℝ) * hkR`. Rewrite using `[(h4 w hw).2 τ hτ, hinfπ, Multiset.map_map, Multiset.map_map]`. Take `⟨h, h1', h2', -⟩` from `eta_inf D hAut ((D.naut.iotaQC i).toRingHom.comp τ)`.

Rewrite using `[h1', h2', Multiset.sum_singleton, Multiset.sum_singleton]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Use `push_cast`. Take the linear combination `hkC / 2`.
-/
theorem GlobalTheory.HalfTwist.exists_galRep_halfTwist : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (e : ℤ), D.naut.csd π → (∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ z ∈ D.naut.infG π τ, ∃ k : ℤ, z + (e : ℂ) / 2 = (k : ℂ)) → ∃ ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((e : ℝ) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infG π ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (e : ℂ) / 2))) := by
  intro D htie hadm i a ha π e hcsd hinf
  obtain ⟨hLP, hAut, hGal⟩ := htie
  obtain ⟨hG1, -, hG3⟩ := hadm i
  have hoff : ∀ {b : ℕ} (ρ : GE D.nd →* GL (Fin b) (Qbar (D.nd.l i))) (f : ∀ w, D.naut.LP w),
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = f w) →
      (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.wdOf i ρ w = f w) → ∀ w, D.naut.wdOf i ρ w = f w := by
    intro b ρ f h1 h2 w
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · exact h2 w hw
    · exact h1 w hw
  rcases Int.even_or_odd (e + (a : ℤ) - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  ·
    have hkC : (e : ℂ) + (a : ℂ) - 1 = (k : ℂ) + (k : ℂ) := by exact_mod_cast hk
    have hkR : (e : ℝ) + (a : ℝ) - 1 = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
    have hralg : D.naut.ralg π := by
      rw [D.naut.ralg_def]
      intro τ
      refine ⟨(hinf τ).1, fun z hz => ?_⟩
      obtain ⟨m, hm⟩ := (hinf τ).2 z hz
      exact ⟨m - k, by push_cast; linear_combination hm - hkC / 2⟩
    obtain ⟨ρ₀, hc0, hss0, hoff0, hon0⟩ := hG1 a ha π hcsd hralg
    have hinf0 : ∀ τ, D.naut.infG (D.naut.tw D.naut.etaT D.naut.etaTinv) τ = {0} := by
      intro τ
      obtain ⟨h, h1, h2, -⟩ := eta_inf D hAut τ
      rw [D.naut.infG_tw _ _ τ (-h) h2, h1, Multiset.map_singleton, add_neg_cancel]
    obtain ⟨ρχ, hcχ, hoffχ, honχ⟩ := hG3 (D.naut.tw D.naut.etaT D.naut.etaTinv) (k : ℝ) (fun τ z hz => by
      rw [hinf0, Multiset.mem_singleton] at hz
      exact ⟨k, by rw [hz]; push_cast; ring⟩)
    obtain ⟨ρ', h1, h2, h3, h4⟩ := GlobalTheory.T.galois_rep_weil_jumps D ⟨hLP, hAut, hGal⟩ i a ρ₀ ρχ
      (fun w => D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))
      (fun w => D.naut.lpTw (D.naut.locG (D.naut.tw D.naut.etaT D.naut.etaTinv) w) (k : ℝ))
      (fun τ => (D.naut.infG π τ).map (fun z => -z + ((a : ℂ) - 1) / 2))
      (fun _ => -(k : ℂ))
      ⟨hc0, hss0, hoff ρ₀ _ (fun w hw => (hoff0 w hw).1) (fun w hw => (hon0 w hw).2.2),
        fun w hw => ⟨(hon0 w hw).1, fun τ hτ => by rw [(hon0 w hw).2.1 τ hτ, D.naut.jumpsInf_def i π τ hralg]⟩⟩
      ⟨hcχ, isSSRep_rank_one ρχ, hoff ρχ _ hoffχ (fun w hw => (honχ w hw).2.1),
        fun w hw => ⟨(honχ w hw).1, fun τ hτ => by
          rw [(honχ w hw).2.2 τ hτ, hinf0, Multiset.map_singleton, zero_add]
          push_cast
          rfl⟩⟩
    refine ⟨ρ', h1, h2, fun w => ?_, fun w hw => ⟨(h4 w hw).1, fun τ hτ => ?_⟩⟩
    · rw [h3 w]
      have hU : D.naut.lpDim (D.naut.lpUnr w {1}) = 1 := by
        rw [(D.naut.lpUnr_spec w {1} (by simp)).2.2, Multiset.card_singleton]
      rw [D.naut.locG_tw, eta_char,
        (hLP w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))
          (D.naut.lpUnr w {1}) (D.naut.lpUnr w {1}) (k : ℝ) hU hU).2.2.1,
        (hLP w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))
          (D.naut.lpUnr w {1}) (D.naut.lpUnr w {1}) (k : ℝ) hU hU).2.2.2.2.1,
        D.naut.lpTw_add]
      congr 1
      linear_combination (-1 / 2 : ℝ) * hkR
    · rw [(h4 w hw).2 τ hτ, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]
      linear_combination hkC / 2
  ·
    have hkC : (e : ℂ) + (a : ℂ) - 1 = 2 * (k : ℂ) + 1 := by exact_mod_cast hk
    have hkR : (e : ℝ) + (a : ℝ) - 1 = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    have hcsd' : D.naut.csd (D.naut.tw π D.naut.etaT) := D.naut.csd_tw π D.naut.etaT hAut.1.1 hcsd
    have hinfπ : ∀ τ, D.naut.infG (D.naut.tw π D.naut.etaT) τ =
        (D.naut.infG π τ).map (· + (D.naut.infG D.naut.etaT τ).sum) := by
      intro τ
      obtain ⟨h, h1, -, -⟩ := eta_inf D hAut τ
      rw [D.naut.infG_tw π D.naut.etaT τ h h1, h1, Multiset.sum_singleton]
    have hralg : D.naut.ralg (D.naut.tw π D.naut.etaT) := by
      rw [D.naut.ralg_def]
      intro τ
      obtain ⟨h, h1, -, hh⟩ := eta_inf D hAut τ
      rw [D.naut.infG_tw π D.naut.etaT τ h h1]
      refine ⟨(hinf τ).1.map (add_left_injective h), fun z' hz' => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
      obtain ⟨m, hm⟩ := (hinf τ).2 z hz
      rcases hh with rfl | rfl
      · exact ⟨m - k, by push_cast; linear_combination hm - hkC / 2⟩
      · exact ⟨m - k - 1, by push_cast; linear_combination hm - hkC / 2⟩
    obtain ⟨ρ₀, hc0, hss0, hoff0, hon0⟩ := hG1 a ha _ hcsd' hralg
    obtain ⟨ρχ, hcχ, hoffχ, honχ⟩ := hG3 D.naut.etaTinv ((k : ℝ) + 1 / 2) (fun τ z hz => by
      obtain ⟨h, -, h2, hh⟩ := eta_inf D hAut τ
      rw [h2, Multiset.mem_singleton] at hz
      rcases hh with rfl | rfl
      · exact ⟨k, by rw [hz]; push_cast; ring⟩
      · exact ⟨k + 1, by rw [hz]; push_cast; ring⟩)
    obtain ⟨ρ', h1, h2, h3, h4⟩ := GlobalTheory.T.galois_rep_weil_jumps D ⟨hLP, hAut, hGal⟩ i a ρ₀ ρχ
      (fun w => D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaT) w) ((1 - (a : ℝ)) / 2))
      (fun w => D.naut.lpTw (D.naut.locG D.naut.etaTinv w) ((k : ℝ) + 1 / 2))
      (fun τ => (D.naut.infG (D.naut.tw π D.naut.etaT) τ).map (fun z => -z + ((a : ℂ) - 1) / 2))
      (fun τ => -((D.naut.infG D.naut.etaTinv τ).sum + (((k : ℝ) + 1 / 2 : ℝ) : ℂ)))
      ⟨hc0, hss0, hoff ρ₀ _ (fun w hw => (hoff0 w hw).1) (fun w hw => (hon0 w hw).2.2),
        fun w hw => ⟨(hon0 w hw).1, fun τ hτ => by rw [(hon0 w hw).2.1 τ hτ, D.naut.jumpsInf_def i _ τ hralg]⟩⟩
      ⟨hcχ, isSSRep_rank_one ρχ, hoff ρχ _ hoffχ (fun w hw => (honχ w hw).2.1),
        fun w hw => ⟨(honχ w hw).1, fun τ hτ => by
          rw [(honχ w hw).2.2 τ hτ]
          obtain ⟨h, -, h2, -⟩ := eta_inf D hAut ((D.naut.iotaQC i).toRingHom.comp τ)
          rw [h2, Multiset.map_singleton, Multiset.sum_singleton]⟩⟩
    refine ⟨ρ', h1, h2, fun w => ?_, fun w hw => ⟨(h4 w hw).1, fun τ hτ => ?_⟩⟩
    · rw [h3 w]
      have hU : D.naut.lpDim (D.naut.lpUnr w {1}) = 1 := by
        rw [(D.naut.lpUnr_spec w {1} (by simp)).2.2, Multiset.card_singleton]
      have hη : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
      have hη' : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
      rw [D.naut.locG_tw,
        (hLP w (D.naut.lpTw (D.naut.lpChar (D.naut.locG π w) (D.naut.locG D.naut.etaT w)) ((1 - (a : ℝ)) / 2))
          (D.naut.locG π w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w)
          ((k : ℝ) + 1 / 2) hη' hη').2.2.1,
        (hLP w (D.naut.lpChar (D.naut.locG π w) (D.naut.locG D.naut.etaT w))
          (D.naut.locG π w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w)
          ((1 - (a : ℝ)) / 2) hη' hη').2.1,
        (hLP w (D.naut.locG π w) (D.naut.locG π w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w)
          0 hη hη').2.2.2.1,
        eta_char,
        (hLP w (D.naut.locG π w) (D.naut.locG π w) (D.naut.lpUnr w {1}) (D.naut.lpUnr w {1}) 0 hU hU).2.2.2.2.1,
        D.naut.lpTw_add]
      congr 1
      linear_combination (-1 / 2 : ℝ) * hkR
    · rw [(h4 w hw).2 τ hτ, hinfπ, Multiset.map_map, Multiset.map_map]
      obtain ⟨h, h1', h2', -⟩ := eta_inf D hAut ((D.naut.iotaQC i).toRingHom.comp τ)
      rw [h1', h2', Multiset.sum_singleton, Multiset.sum_singleton]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]
      push_cast
      linear_combination hkC / 2
