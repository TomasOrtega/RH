import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLq.DetSplit

open GlobalTheory.GLq Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Take `⟨R, hR, he⟩` from `GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hα hA hαA`. Rewrite using `[he, GlobalTheory.GLq.LabelMul.hc_add_left]`. Establish `hc` using `(GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1`. Conclude with `GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hα) hβ) (hc R β hR hβ) h`.
-/
theorem ip_hc_mono_left (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α A : Gn g m → ℂ) (hα : IsIrr α) (hA : IsChar A) (hαA : ip α A ≠ 0)
    (β : Gn g k → ℂ) (hβ : IsChar β) (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k A β n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hα hA hαA
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hα) hβ) (hc R β hR hβ) h

/- English proof (translation)
Take `⟨R, hR, he⟩` from `GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hβ hB hβB`. Rewrite using `[he, GlobalTheory.GLq.LabelMul.hc_add_right]`. Establish `hc` using `(GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1`. Conclude with `GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β hα (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ)) (hc α R hα hR) h`.
-/
theorem ip_hc_mono_right (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α : Gn g m → ℂ) (hα : IsChar α) (β B : Gn g k → ℂ) (hβ : IsIrr β) (hB : IsChar B) (hβB : ip β B ≠ 0)
    (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k α B n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hβ hB hβB
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β hα (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ)) (hc α R hα hR) h

/- English proof (translation)
Substitute `e₁ e₂` using the available equality. Conclude with `GlobalTheory.GLq.LabelMul.hcL_append K₁ K₂ (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₁ q hq)) (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₂ q hq)) n hn`.
-/
theorem hcL_append_of (K₁ K₂ : List (Pc g)) (h₁ : ∀ q ∈ K₁, IsCusp q.2) (h₂ : ∀ q ∈ K₂, IsCusp q.2)
    (m₁ m₂ n : ℕ) (e₁ : degL K₁ = m₁) (e₂ : degL K₂ = m₂) (hn : n = m₁ + m₂) :
    hcL (K₁ ++ K₂) n = hc m₁ m₂ (hcL K₁ m₁) (hcL K₂ m₂) n := by
  subst e₁ e₂
  exact GlobalTheory.GLq.LabelMul.hcL_append K₁ K₂ (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₁ q hq))
    (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₂ q hq)) n hn

/- English proof (translation)
Introduce `p _ L r a c θ u f ψ α β σ hr hψ hα hβ hσ hL hlab hψαβ hασ`. Take `⟨Q, hQ, hQd, rfl, hQi⟩` from `hL`. Take `⟨Kσ, hKσ, hKσd, hKσi⟩` from `GlobalTheory.GLq.SuppCusp.exists_cusp_list p a σ hσ`. Take `⟨Kβ, hKβ, hKβd, hKβi⟩` from `GlobalTheory.GLq.SuppCusp.exists_cusp_list p c β hβ`. Establish `hθI : IsIrr (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))` using `GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)`.

Establish `hθC` using `GlobalTheory.GLq.LabelMul.isChar_of_isIrr hθI`. Establish `hθcusp : IsCusp (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))` using `⟨one_pos, hθI, fun a h1 h2 => by omega⟩`. Establish `hQc : ∀ q ∈ Q.map Prod.snd, IsCusp q.2`. Introduce `q hq`. Take `⟨q', hq', rfl⟩` from `List.mem_map.1 hq`.

Conclude with `(hQ q' hq').2.1`. Establish `hA` using `GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hQc _ hQd`. Establish `fin : ∀ K' : List (Pc p), (Q.map Prod.snd).Perm K' → (⟨1, fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc p) ∈ K' → ((Q.map Prod.fst).prod).IsRoot u`. Introduce `K' hp hm`. Take `⟨⟨P, s⟩, hq, hs⟩` from `List.mem_map.1 (hp.mem_iff.2 hm)`.

Simplify using `only at hs`. Substitute `hs` using the available equality. Establish `hP` using `GlobalTheory.GLq.DetRoot.eq_of_isCuspOf_det L θ u hlab P (hQ _ hq)`. Establish `hdvd : P ∣ (Q.map Prod.fst).prod` using `List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)`. Conclude with `Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd`.

Generalize the expression as in `(fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) = θd at hθI hθC hθcusp hασ fin`. Establish `h1` using `GlobalTheory.GLq.DetRoot.ip_hc_left a α hα σ hσ θd hθC Kσ hKσ hKσd hKσi hασ`. Establish `hT : ∀ q ∈ [(⟨1, θd⟩ : Pc p)], IsCusp q.2`. Introduce `q hq`. Rewrite `hq` using `[List.mem_singleton]`.

Substitute `hq` using the available equality. Conclude with `hθcusp`. Establish `hTd : degL [(⟨1, θd⟩ : Pc p)] = 1` using `by simp [degL]`. Establish `eα : hcL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) (a + 1) = hc a 1 (hcL Kσ a) θd (a + 1)`. Rewrite using `[hcL_append_of Kσ _ hKσ hT a 1 (a + 1) hKσd hTd rfl, GlobalTheory.GLq.IpCuspProd.hcL_single 1 θd (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hθC)]`.

Rewrite `h1` using `[← eα]`. Establish `hKα : ∀ q ∈ Kσ ++ [(⟨1, θd⟩ : Pc p)], IsCusp q.2`. Introduce `q hq`. Break down `List.mem_append.1 hq with hq | hq` into its components or cases. Conclude with `hKσ q hq`.

Conclude with `hT q hq`. Establish `hKαd : degL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) = a + 1`. Rewrite using `[GlobalTheory.GLq.LabelMul.degL_append, hKσd, hTd]`. Establish `hAα` using `GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKα _ hKαd`. Establish `h2` using `ip_hc_mono_left (a + 1) c r hr ψ hψ α _ hα hAα h1 β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ) hψαβ`.

Establish `h3` using `ip_hc_mono_right (a + 1) c r hr ψ hψ _ hAα β (hcL Kβ c) hβ (GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKβ _ hKβd) hKβi h2`. Rewrite `h3` using `[← hcL_append_of _ Kβ hKα hKβ (a + 1) c r hKαd hKβd hr]`. Establish `hKall : ∀ q ∈ (Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ, IsCusp q.2`. Introduce `q hq`. Break down `List.mem_append.1 hq with hq | hq` into its components or cases.

Conclude with `hKα q hq`. Conclude with `hKβ q hq`. Establish `hKd : degL ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) = r`. Rewrite using `[GlobalTheory.GLq.LabelMul.degL_append, hKαd, hKβd, hr]`. Establish `hB` using `GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKall _ hKd`.

Establish `hAB` using `GlobalTheory.GLq.DetRoot.ip_ne_zero_of_common hψ hA hB hQi h3`. Use `fin ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) ?_ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp p _ _ _ hQd hKd hQc hKall).1 hn)`.
-/
theorem root_of_constituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  intro p _ L r a c θ u f ψ α β σ hr hψ hα hβ hσ hL hlab hψαβ hασ
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨Kσ, hKσ, hKσd, hKσi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p a σ hσ
  obtain ⟨Kβ, hKβ, hKβd, hKβi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p c β hβ
  have hθI : IsIrr (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hθC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hθI
  have hθcusp : IsCusp (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hθI, fun a h1 h2 => by omega⟩
  have hQc : ∀ q ∈ Q.map Prod.snd, IsCusp q.2 := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact (hQ q' hq').2.1
  have hA := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hQc _ hQd
  have fin : ∀ K' : List (Pc p), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc p) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot u := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := GlobalTheory.GLq.DetRoot.eq_of_isCuspOf_det L θ u hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  generalize (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) = θd at hθI hθC hθcusp hασ fin
  have h1 := GlobalTheory.GLq.DetRoot.ip_hc_left a α hα σ hσ θd hθC Kσ hKσ hKσd hKσi hασ
  have hT : ∀ q ∈ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hθcusp
  have hTd : degL [(⟨1, θd⟩ : Pc p)] = 1 := by simp [degL]
  have eα : hcL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) (a + 1) = hc a 1 (hcL Kσ a) θd (a + 1) := by
    rw [hcL_append_of Kσ _ hKσ hT a 1 (a + 1) hKσd hTd rfl,
      GlobalTheory.GLq.IpCuspProd.hcL_single 1 θd (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hθC)]
  rw [← eα] at h1
  have hKα : ∀ q ∈ Kσ ++ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKσ q hq
    · exact hT q hq
  have hKαd : degL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) = a + 1 := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKσd, hTd]
  have hAα := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKα _ hKαd
  have h2 := ip_hc_mono_left (a + 1) c r hr ψ hψ α _ hα hAα h1 β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ) hψαβ
  have h3 := ip_hc_mono_right (a + 1) c r hr ψ hψ _ hAα β (hcL Kβ c) hβ
    (GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKβ _ hKβd) hKβi h2
  rw [← hcL_append_of _ Kβ hKα hKβ (a + 1) c r hKαd hKβd hr] at h3
  have hKall : ∀ q ∈ (Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ, IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKα q hq
    · exact hKβ q hq
  have hKd : degL ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) = r := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKαd, hKβd, hr]
  have hB := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKall _ hKd
  have hAB := GlobalTheory.GLq.DetRoot.ip_ne_zero_of_common hψ hA hB hQi h3
  refine fin ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) ?_ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))
  by_contra hn
  exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp p _ _ _ hQd hKd hQc hKall).1 hn)

end GlobalTheory.GLq.DetSplit
