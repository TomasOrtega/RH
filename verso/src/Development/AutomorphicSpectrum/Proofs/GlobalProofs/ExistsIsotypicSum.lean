import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def IsIrrK (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStable G π S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S

def isoGens (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Set (Submodule ℂ H) :=
  {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ maxCpt G, ∀ w ∈ S, T (π k w) = π k (T w)}

/- English proof (translation)
Introduce `k hk y hy`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `s hs`. Establish `hk' : star k ∈ maxCpt G` using `⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩`. Establish `h1 : π k (π (star k) s) = s`.

Establish `hm : k * star k = 1` using `Matrix.mem_unitaryGroup_iff.1 hk.2`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hA.1.2 k hk.1 (star k) hk'.1, hm, hA.1.1]`. Both sides reduce to the same expression. Set `Lk : H →ₗᵢ[ℂ] H` to `⟨(π k : H →ₗ[ℂ] H), hA.2.2.1 k hk⟩`. Establish `h2 : inner ℂ (π k (π (star k) s)) (π k y) = inner ℂ (π (star k) s) y` using `Lk.inner_map_map _ _`.

Rewrite using `[← h1, h2]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (hS _ hk' s hs) hy`.
-/
theorem orthogonal_kstable (hG : IsLinRed G) (hA : IsAdmOn G π) {S : Submodule ℂ H}
    (hS : IsKStable G π S) : IsKStable G π Sᗮ := by
  intro k hk y hy
  rw [Submodule.mem_orthogonal]
  intro s hs
  have hk' : star k ∈ maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
  have h1 : π k (π (star k) s) = s := by
    have hm : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    rw [← ContinuousLinearMap.comp_apply, ← hA.1.2 k hk.1 (star k) hk'.1, hm, hA.1.1]
    rfl
  let Lk : H →ₗᵢ[ℂ] H := ⟨(π k : H →ₗ[ℂ] H), hA.2.2.1 k hk⟩
  have h2 : inner ℂ (π k (π (star k) s)) (π k y) = inner ℂ (π (star k) s) y := Lk.inner_map_map _ _
  rw [← h1, h2]
  exact Submodule.inner_right_of_mem_orthogonal (hS _ hk' s hs) hy

/- English proof (translation)
Introduce `k hk w hw`. Establish `h : sSup A ≤ (sSup A).comap (π k : H →ₗ[ℂ] H)` using `sSup_le fun S hS x hx => Submodule.mem_comap.2 (le_sSup hS (hA S hS k hk x hx))`. Conclude with `h hw`.
-/
theorem sSup_kstable {A : Set (Submodule ℂ H)} (hA : ∀ S ∈ A, IsKStable G π S) :
    IsKStable G π (sSup A) := by
  intro k hk w hw
  have h : sSup A ≤ (sSup A).comap (π k : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => Submodule.mem_comap.2 (le_sSup hS (hA S hS k hk x hx))
  exact h hw

/- English proof (translation)
Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `S hfin hm hS`. Distinguish the cases in `hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S`. Use `⟨{S}, Set.finite_singleton S, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `I rfl`. Conclude with `⟨hfin, hS, hirr⟩`. Simplify using the standard rewrite rules. Use `push_neg at hirr`. Take `⟨S', hle, hS', hne0, hneS⟩` from `hirr`.

Use `haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle`. Establish `hlt : S' < S` using `lt_of_le_of_ne hle hneS`. Establish `hT : IsKStable G π (S ⊓ S'ᗮ)` using `fun k hk v hv => ⟨hS k hk v hv.1, orthogonal_kstable hG hA hS' k hk v hv.2⟩`. Use `haveI : FiniteDimensional ℂ (S ⊓ S'ᗮ : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_left`. Establish `hltT : S ⊓ S'ᗮ < S`.

Use `lt_of_le_of_ne inf_le_left fun h => hne0 ?_` and prove the remaining obligations. Establish `hSo : S ≤ S'ᗮ` using `inf_eq_left.1 h`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `h0 : ⟪x, x⟫_ℂ = 0` using `Submodule.inner_right_of_mem_orthogonal hx (hSo (hle hx))`.

Conclude with `(Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 h0)`. Establish `hd₁ : Module.finrank ℂ S' < m` using `hm ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Establish `hd₂ : Module.finrank ℂ (S ⊓ S'ᗮ : Submodule ℂ H) < m` using `hm ▸ Submodule.finrank_lt_finrank_of_lt hltT`. Take `⟨F₁, hF₁, hI₁, hle₁⟩` from `ih _ hd₁ S' inferInstance rfl hS'`. Take `⟨F₂, hF₂, hI₂, hle₂⟩` from `ih _ hd₂ (S ⊓ S'ᗮ) inferInstance rfl hT`.

Use `⟨F₁ ∪ F₂, hF₁.union hF₂, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `I (hI | hI)`. Conclude with `hI₁ I hI`. Conclude with `hI₂ I hI`. Introduce `v hv`.

Establish `hp : ((S'.orthogonalProjection v : S') : H) ∈ S'` using `(S'.orthogonalProjection v).2`. Establish `hq : v - (S'.orthogonalProjection v : H) ∈ S ⊓ S'ᗮ` using `⟨S.sub_mem hv (hle hp), Submodule.sub_starProjection_mem_orthogonal (K := S') v⟩`. Establish `e : v = (S'.orthogonalProjection v : H) + (v - (S'.orthogonalProjection v : H))` using `by abel`. Rewrite using `[e, sSup_union]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (hle₁ hp)) (Submodule.mem_sup_right (hle₂ hq))`.
-/
theorem exists_irr_family (hG : IsLinRed G) (hA : IsAdmOn G π) (m : ℕ) :
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Module.finrank ℂ S = m → IsKStable G π S →
      ∃ F : Set (Submodule ℂ H), F.Finite ∧ (∀ I ∈ F, IsIrrK G π I) ∧ S ≤ sSup F := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hfin hm hS
    by_cases hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S
    · refine ⟨{S}, Set.finite_singleton S, ?_, ?_⟩
      · rintro I rfl
        exact ⟨hfin, hS, hirr⟩
      · simp
    · push_neg at hirr
      obtain ⟨S', hle, hS', hne0, hneS⟩ := hirr
      haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
      have hlt : S' < S := lt_of_le_of_ne hle hneS
      have hT : IsKStable G π (S ⊓ S'ᗮ) := fun k hk v hv =>
        ⟨hS k hk v hv.1, orthogonal_kstable hG hA hS' k hk v hv.2⟩
      haveI : FiniteDimensional ℂ (S ⊓ S'ᗮ : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_left
      have hltT : S ⊓ S'ᗮ < S := by
        refine lt_of_le_of_ne inf_le_left fun h => hne0 ?_
        have hSo : S ≤ S'ᗮ := inf_eq_left.1 h
        rw [eq_bot_iff]
        intro x hx
        have h0 : ⟪x, x⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hx (hSo (hle hx))
        exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 h0)
      have hd₁ : Module.finrank ℂ S' < m := hm ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hd₂ : Module.finrank ℂ (S ⊓ S'ᗮ : Submodule ℂ H) < m :=
        hm ▸ Submodule.finrank_lt_finrank_of_lt hltT
      obtain ⟨F₁, hF₁, hI₁, hle₁⟩ := ih _ hd₁ S' inferInstance rfl hS'
      obtain ⟨F₂, hF₂, hI₂, hle₂⟩ := ih _ hd₂ (S ⊓ S'ᗮ) inferInstance rfl hT
      refine ⟨F₁ ∪ F₂, hF₁.union hF₂, ?_, ?_⟩
      · rintro I (hI | hI)
        · exact hI₁ I hI
        · exact hI₂ I hI
      · intro v hv
        have hp : ((S'.orthogonalProjection v : S') : H) ∈ S' := (S'.orthogonalProjection v).2
        have hq : v - (S'.orthogonalProjection v : H) ∈ S ⊓ S'ᗮ :=
          ⟨S.sub_mem hv (hle hp), Submodule.sub_starProjection_mem_orthogonal (K := S') v⟩
        have e : v = (S'.orthogonalProjection v : H) + (v - (S'.orthogonalProjection v : H)) := by abel
        rw [e, sSup_union]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hle₁ hp)) (Submodule.mem_sup_right (hle₂ hq))

/- English proof (translation)
Take `⟨T, rfl, hT⟩` from `h`. Introduce and unpack `k hk _ ⟨s, hs, rfl⟩`. Conclude with `⟨π k s, hS k hk s hs, hT k hk s hs⟩`.
-/
theorem isoGens_kstable {S S' : Submodule ℂ H} (hS : IsKStable G π S) (h : S' ∈ isoGens G π S) :
    IsKStable G π S' := by
  obtain ⟨T, rfl, hT⟩ := h
  rintro k hk _ ⟨s, hs, rfl⟩
  exact ⟨π k s, hS k hk s hs, hT k hk s hs⟩

/- English proof (translation)
Use `le_trans (le_of_eq ?_) (le_sSup (show S.map LinearMap.id ∈ isoGens G π S from ⟨LinearMap.id, rfl, fun k _ w _ => rfl⟩))` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem le_sSup_isoGens (S : Submodule ℂ H) : S ≤ sSup (isoGens G π S) := by
  refine le_trans (le_of_eq ?_) (le_sSup (show S.map LinearMap.id ∈ isoGens G π S from
    ⟨LinearMap.id, rfl, fun k _ w _ => rfl⟩))
  simp

/- English proof (translation)
Take `⟨T, rfl, hT⟩` from `h`. Take `⟨s, hs, rfl⟩` from `hx`. Establish `hTY : ∀ w ∈ S, T w ∈ Y` using `fun w hw => hSY (le_sSup (show S.map T ∈ isoGens G π S from ⟨T, rfl, hT⟩) ⟨w, hw, rfl⟩)`. Set `f : S →ₗ[ℂ] H` to `D ∘ₗ (T.domRestrict S).codRestrict Y (fun w => hTY w w.2)`. Take `⟨T', hT'⟩` from `LinearMap.exists_extend f`.

Establish `hval : ∀ w (hw : w ∈ S), T' w = D ⟨T w, hTY w hw⟩` using `fun w hw => LinearMap.congr_fun hT' ⟨w, hw⟩`. Establish `hcomm : ∀ k ∈ maxCpt G, ∀ w ∈ S, T' (π k w) = π k (T' w)`. Introduce `k hk w hw`. Rewrite using `[hval _ (hS k hk w hw), hval w hw]`. Conclude with `hD k hk _ _ (hT k hk w hw)`.

Establish `hmem : S.map T' ∈ isoGens G π S` using `⟨T', rfl, hcomm⟩`. Establish `: T' s ∈ Y` using `hSY (le_sSup hmem ⟨s, hs, rfl⟩)`. Rewrite `this` using `[hval s hs]`. Then use the resulting hypothesis.
-/
theorem map_mem_of_gen {Y S S' : Submodule ℂ H} (hSY : sSup (isoGens G π S) ≤ Y) (h : S' ∈ isoGens G π S)
    (D : Y →ₗ[ℂ] H) (hD : ∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y))
    (hS : IsKStable G π S) {x : H} (hx : x ∈ S') (hxY : x ∈ Y) : D ⟨x, hxY⟩ ∈ Y := by
  obtain ⟨T, rfl, hT⟩ := h
  obtain ⟨s, hs, rfl⟩ := hx
  have hTY : ∀ w ∈ S, T w ∈ Y := fun w hw =>
    hSY (le_sSup (show S.map T ∈ isoGens G π S from ⟨T, rfl, hT⟩) ⟨w, hw, rfl⟩)
  let f : S →ₗ[ℂ] H := D ∘ₗ (T.domRestrict S).codRestrict Y (fun w => hTY w w.2)
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend f
  have hval : ∀ w (hw : w ∈ S), T' w = D ⟨T w, hTY w hw⟩ := fun w hw =>
    LinearMap.congr_fun hT' ⟨w, hw⟩
  have hcomm : ∀ k ∈ maxCpt G, ∀ w ∈ S, T' (π k w) = π k (T' w) := by
    intro k hk w hw
    rw [hval _ (hS k hk w hw), hval w hw]
    exact hD k hk _ _ (hT k hk w hw)
  have hmem : S.map T' ∈ isoGens G π S := ⟨T', rfl, hcomm⟩
  have : T' s ∈ Y := hSY (le_sSup hmem ⟨s, hs, rfl⟩)
  rwa [hval s hs] at this

/- English proof (translation)
Introduce `n G H _ _ _ π hG hA v hv`. Take `⟨S, hfin, hvS, hS⟩` from `hv`. Take `⟨F, hF, hI, hle⟩` from `exists_irr_family hG hA _ S hfin rfl hS`. Set `iso : Submodule ℂ H → Submodule ℂ H` to `fun I => sSup (isoGens G π I)`. Establish `hisoK : ∀ I ∈ F, IsKStable G π (iso I)` using `fun I hIF => sSup_kstable fun S' h => isoGens_kstable (hI I hIF).2.1 h`.

Establish `hisoF : ∀ I ∈ F, FiniteDimensional ℂ (iso I)` using `fun I hIF => hA.2.2.2 I (hI I hIF).1 (hI I hIF).2.1 (hI I hIF).2.2`. Establish `hYle : ∀ I ∈ F, iso I ≤ sSup (iso '' F)` using `fun I hIF => le_sSup ⟨I, hIF, rfl⟩`. Use `⟨sSup (iso '' F), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sSup_eq_iSup'] haveI : Finite ↥(iso '' F) := (hF.image iso).to_subtype haveI : ∀ a : ↥(iso '' F), FiniteDimensional ℂ (a : Submodule ℂ H) := by`. Introduce and unpack `⟨_, I, hIF, rfl⟩`.

Conclude with `hisoF I hIF`. Conclude with `Submodule.finiteDimensional_iSup _`. Conclude with `(sSup_le fun I hIF => (le_sSup_isoGens I).trans (hYle I hIF)) (hle hvS)`. Use `sSup_kstable ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨I, hIF, rfl⟩`.

Conclude with `hisoK I hIF`. Introduce `D hD y`. Establish `hP : sSup (iso '' F) ≤ ((sSup (iso '' F)).comap D).map (sSup (iso '' F)).subtype`. Use `sSup_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨I, hIF, rfl⟩`.

Use `sSup_le fun S' hS' x hx => ?_` and prove the remaining obligations. Establish `hxY : x ∈ sSup (iso '' F)` using `hYle I hIF (le_sSup hS' hx)`. Conclude with `⟨⟨x, hxY⟩, map_mem_of_gen (hYle I hIF) hS' D hD (hI I hIF).2.1 hx hxY, rfl⟩`. Take `⟨y', hy', he⟩` from `hP y.2`. Establish `hyy : y' = y` using `Subtype.ext he`.

Substitute `hyy` using the available equality. Conclude with `hy'`.
-/
theorem exists_isotypic_sum : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y := by
  intro n G H _ _ _ π hG hA v hv
  obtain ⟨S, hfin, hvS, hS⟩ := hv
  obtain ⟨F, hF, hI, hle⟩ := exists_irr_family hG hA _ S hfin rfl hS
  let iso : Submodule ℂ H → Submodule ℂ H := fun I => sSup (isoGens G π I)
  have hisoK : ∀ I ∈ F, IsKStable G π (iso I) := fun I hIF =>
    sSup_kstable fun S' h => isoGens_kstable (hI I hIF).2.1 h
  have hisoF : ∀ I ∈ F, FiniteDimensional ℂ (iso I) := fun I hIF =>
    hA.2.2.2 I (hI I hIF).1 (hI I hIF).2.1 (hI I hIF).2.2
  have hYle : ∀ I ∈ F, iso I ≤ sSup (iso '' F) := fun I hIF => le_sSup ⟨I, hIF, rfl⟩
  refine ⟨sSup (iso '' F), ?_, ?_, ?_, ?_⟩
  · rw [sSup_eq_iSup']
    haveI : Finite ↥(iso '' F) := (hF.image iso).to_subtype
    haveI : ∀ a : ↥(iso '' F), FiniteDimensional ℂ (a : Submodule ℂ H) := by
      rintro ⟨_, I, hIF, rfl⟩
      exact hisoF I hIF
    exact Submodule.finiteDimensional_iSup _
  · exact (sSup_le fun I hIF => (le_sSup_isoGens I).trans (hYle I hIF)) (hle hvS)
  · refine sSup_kstable ?_
    rintro _ ⟨I, hIF, rfl⟩
    exact hisoK I hIF
  · intro D hD y
    have hP : sSup (iso '' F) ≤ ((sSup (iso '' F)).comap D).map (sSup (iso '' F)).subtype := by
      refine sSup_le ?_
      rintro _ ⟨I, hIF, rfl⟩
      refine sSup_le fun S' hS' x hx => ?_
      have hxY : x ∈ sSup (iso '' F) := hYle I hIF (le_sSup hS' hx)
      exact ⟨⟨x, hxY⟩, map_mem_of_gen (hYle I hIF) hS' D hD (hI I hIF).2.1 hx hxY, rfl⟩
    obtain ⟨y', hy', he⟩ := hP y.2
    have hyy : y' = y := Subtype.ext he
    subst hyy
    exact hy'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

end
