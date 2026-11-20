import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul

open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Use `haveI : (H.subgroupOf L).FiniteIndex := ⟨hfin⟩`. Set `f : L ⧸ H.subgroupOf L → K ⧸ H.subgroupOf K` to `Quotient.map' (fun l => (⟨l, hLK l.2⟩ : K)) (by`. Introduce `a b hab`. Rewrite `hab`, the goal using `[QuotientGroup.leftRel_apply]`. Simplify `hab)` using `[Subgroup.mem_subgroupOf]`.

Establish `hf : Function.Surjective f`. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H k`. Take `⟨l, hl, h, hh, e⟩` from `hcov k k.2`.

Use `⟨QuotientGroup.mk ⟨l, hl⟩, ?_⟩` and prove the remaining obligations. Use `show QuotientGroup.mk _ = QuotientGroup.mk k`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify `hh` using `[e]`. Use `haveI := Finite.of_surjective f hf`.

Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
private theorem relIndex_ne_zero_of_cover_ordinary_hecke_characters {G : Type} [Group G] (H K L : Subgroup G) (hHK : H ≤ K) (hLK : L ≤ K)
    (hcov : ∀ k ∈ K, ∃ l ∈ L, ∃ h ∈ H, k = l * h) (hfin : H.relIndex L ≠ 0) : H.relIndex K ≠ 0 := by
  haveI : (H.subgroupOf L).FiniteIndex := ⟨hfin⟩
  let f : L ⧸ H.subgroupOf L → K ⧸ H.subgroupOf K :=
    Quotient.map' (fun l => (⟨l, hLK l.2⟩ : K)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      simpa [Subgroup.mem_subgroupOf] using hab)
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨l, hl, h, hh, e⟩ := hcov k k.2
      refine ⟨QuotientGroup.mk ⟨l, hl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [e] using hh
  haveI := Finite.of_surjective f hf
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Establish `hNm : I.Nm c ≤ I.Iw c` using `le_sup_right`. Establish `hT : I.T ≤ I.Iw c` using `le_trans le_sup_right le_sup_left`. Establish `hN : I.N ≤ I.Iw c` using `le_trans le_sup_left le_sup_left`. Use `relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.Iw c) (I.Iw 0) (I.Nm 0) ?_ le_sup_right ?_ ?_` and prove the remaining obligations. Use `show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0`.

Conclude with `sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _`. Introduce `g hg`. Take `⟨x, hx, t, ht, y, hy, e⟩` from `((iwMem G I 0 g⁻¹).1).1 (inv_mem hg)`. Use `⟨y⁻¹, inv_mem hy, t⁻¹ * x⁻¹, mul_mem (hT (inv_mem ht)) (hN (inv_mem hx)), ?_⟩` and prove the remaining obligations. Rewrite using `[← inv_inv g, e]`.

Use `group`. Introduce `h0`. Apply `I.fin_Nm c` to reduce the goal to its premises. Establish `hd` using `Subgroup.relIndex_dvd_of_le_left (I.Nm 0) hNm`. Rewrite `hd` using `[h0]`.

Conclude with `Nat.eq_zero_of_zero_dvd hd`.
-/
private theorem iwahori_relIndex_ne_zero {G : Type} [Group G] (I : Iwa G) (c : ℕ) : (I.Iw c).relIndex (I.Iw 0) ≠ 0 := by
  have hNm : I.Nm c ≤ I.Iw c := le_sup_right
  have hT : I.T ≤ I.Iw c := le_trans le_sup_right le_sup_left
  have hN : I.N ≤ I.Iw c := le_trans le_sup_left le_sup_left
  refine relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.Iw c) (I.Iw 0) (I.Nm 0) ?_ le_sup_right ?_ ?_
  · show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0
    exact sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _
  · intro g hg
    obtain ⟨x, hx, t, ht, y, hy, e⟩ := ((iwMem G I 0 g⁻¹).1).1 (inv_mem hg)
    refine ⟨y⁻¹, inv_mem hy, t⁻¹ * x⁻¹, mul_mem (hT (inv_mem ht)) (hN (inv_mem hx)), ?_⟩
    rw [← inv_inv g, e]
    group
  · intro h0
    apply I.fin_Nm c
    have hd := Subgroup.relIndex_dvd_of_le_left (I.Nm 0) hNm
    rw [h0] at hd
    exact Nat.eq_zero_of_zero_dvd hd

/- English proof (translation)
Establish `hTc : I.Tc c ≤ I.I1 c` using `le_trans le_sup_right le_sup_left`. Establish `hN1 : I.N ≤ I.I1 c` using `le_trans le_sup_left le_sup_left`. Establish `hNm1 : I.Nm c ≤ I.I1 c` using `le_sup_right`. Establish `hT : I.T ≤ I.Iw c` using `le_trans le_sup_right le_sup_left`. Establish `hle : I.I1 c ≤ I.Iw c` using `by show I.N ⊔ I.Tc c ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm c`.

Conclude with `sup_le_sup_right (sup_le_sup_left (I.Tc_le c) _) _`. Establish `hle' : I.Iw c ≤ I.Iw 0` using `by show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0`. Conclude with `sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _`. Establish `h1 : (I.I1 c).relIndex (I.Iw c) ≠ 0`. Use `relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.I1 c) (I.Iw c) I.T hle hT ?_ ?_` and prove the remaining obligations.

Introduce `g hg`. Take `⟨x, hx, t, ht, y, hy, e⟩` from `((iwMem G I c g).1).1 hg`. Establish `hx' : t⁻¹ * x * t ∈ I.N`. Simplify using `using I.T_N t⁻¹ (inv_mem ht) x hx`. Use `⟨t, ht, t⁻¹ * x * t * y, mul_mem (hN1 hx') (hNm1 hy), ?_⟩` and prove the remaining obligations.

Rewrite using `[e]`. Use `group`. Introduce `h0`. Apply `I.fin_Tc c` to reduce the goal to its premises. Establish `hd` using `Subgroup.relIndex_dvd_of_le_left I.T hTc`.

Rewrite `hd` using `[h0]`. Conclude with `Nat.eq_zero_of_zero_dvd hd`. Rewrite using `[← Subgroup.relIndex_mul_relIndex _ _ _ hle hle']`. Conclude with `mul_ne_zero h1 (iwahori_relIndex_ne_zero I c)`.
-/
private theorem iwahori_pro_unipotent_finite_index {G : Type} [Group G] (I : Iwa G) (c : ℕ) : (I.I1 c).relIndex (I.Iw 0) ≠ 0 := by
  have hTc : I.Tc c ≤ I.I1 c := le_trans le_sup_right le_sup_left
  have hN1 : I.N ≤ I.I1 c := le_trans le_sup_left le_sup_left
  have hNm1 : I.Nm c ≤ I.I1 c := le_sup_right
  have hT : I.T ≤ I.Iw c := le_trans le_sup_right le_sup_left
  have hle : I.I1 c ≤ I.Iw c := by
    show I.N ⊔ I.Tc c ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm c
    exact sup_le_sup_right (sup_le_sup_left (I.Tc_le c) _) _
  have hle' : I.Iw c ≤ I.Iw 0 := by
    show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0
    exact sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _
  have h1 : (I.I1 c).relIndex (I.Iw c) ≠ 0 := by
    refine relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.I1 c) (I.Iw c) I.T hle hT ?_ ?_
    · intro g hg
      obtain ⟨x, hx, t, ht, y, hy, e⟩ := ((iwMem G I c g).1).1 hg
      have hx' : t⁻¹ * x * t ∈ I.N := by
        simpa using I.T_N t⁻¹ (inv_mem ht) x hx
      refine ⟨t, ht, t⁻¹ * x * t * y, mul_mem (hN1 hx') (hNm1 hy), ?_⟩
      rw [e]
      group
    · intro h0
      apply I.fin_Tc c
      have hd := Subgroup.relIndex_dvd_of_le_left I.T hTc
      rw [h0] at hd
      exact Nat.eq_zero_of_zero_dvd hd
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle hle']
  exact mul_ne_zero h1 (iwahori_relIndex_ne_zero I c)

/- English proof (translation)
Introduce `G _ I c`. Conclude with `⟨iwahori_relIndex_ne_zero I c, iwahori_pro_unipotent_finite_index I c⟩`.
-/
theorem UpperTheory.V.Hi.iwFin :
    ∀ (G : Type) [Group G] (I : Iwa G) (c : ℕ), (I.Iw c).relIndex (I.Iw 0) ≠ 0 ∧ (I.I1 c).relIndex (I.Iw 0) ≠ 0 := by
  intro G _ I c
  exact ⟨iwahori_relIndex_ne_zero I c, iwahori_pro_unipotent_finite_index I c⟩
