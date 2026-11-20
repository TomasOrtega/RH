import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

/- English proof (translation)
Take `⟨B, hsym, hpos, hinv⟩` from `hun`. Use `⟨GlobalTheory.CompanionTheory.UnitSemisimple.orth ρ B hinv W, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv hv'`. Establish `h0 : B v v = 0` using `hv' v hv`. Assume the negation of the conclusion as `hne`.

Use `hpos v hne` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Introduce `v`. Take `⟨K, hKo, hKc, hKU⟩` from `hbasis {g | ρ g v = v} ((hs v).mem_nhds (by simp))`.

Establish `hmap : (fixed W.toRepresentation K).map W.toSubmodule.subtype = W.toSubmodule ⊓ fixed ρ K`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `hy' : y ∈ fixed W.toRepresentation K` using `hy`.

Use `⟨y.2, ?_⟩` and prove the remaining obligations. Use `show (y : V) ∈ fixed ρ K`. Rewrite `hy'`, the goal using `[GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff]`. Introduce `k hk`. Use `congrArg Subtype.val (hy' k hk)` as an intermediate fact.

Conclude with `this`. Introduce and unpack `⟨hxW, hx⟩`. Establish `hx' : x ∈ fixed ρ K` using `hx`. Use `⟨⟨x, hxW⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show (⟨x, hxW⟩ : W.toSubmodule) ∈ fixed W.toRepresentation K`.

Rewrite `hx'`, the goal using `[GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff]`. Introduce `k hk`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hx' k hk`. Establish `hfd0 : FiniteDimensional ℂ (fixed W.toRepresentation K)` using `hW.2 K hKo hKc`.

Establish `hfd : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V)`. Rewrite using `[← hmap]`. Use `infer_instance`. Take `⟨t, ht⟩` from `(Submodule.fg_iff_finiteDimensional _).mpr hfd`. Take `⟨w, hw, hperp⟩` from `GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset B hpos t v`.

Rewrite `hw`, `hperp` using `[ht]`. Use `⟨w, hw.1, ?_⟩` and prove the remaining obligations. Use `show ∀ x ∈ W.toSubmodule, B (v - w) x = 0`. Introduce `x hx`. Use `GlobalTheory.CompanionTheory.UnitSemisimple.orthogonal_of_fixed ρ B hinv K hKc W (v - w) ?_ hperp x hx (hs x)` and prove the remaining obligations.

Introduce `k hk`. Establish `hv : ρ k v = v` using `hKU hk`. Establish `hw' : ρ k w = w` using `(GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K w).mp hw.2 k hk`. Simplify using `[map_sub, hv, hw']`.
-/
private theorem exists_compl_of_admissible {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hs : IsSmooth ρ) (hun : IsUnitarisable ρ) (W : Subrepresentation ρ) (hW : IsAdmissible W.toRepresentation) :
    ∃ W' : Subrepresentation ρ, (∀ v, v ∈ W.toSubmodule → v ∈ W'.toSubmodule → v = 0) ∧
      ∀ v, ∃ w ∈ W.toSubmodule, v - w ∈ W'.toSubmodule := by
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  refine ⟨GlobalTheory.CompanionTheory.UnitSemisimple.orth ρ B hinv W, ?_, ?_⟩
  · intro v hv hv'
    have h0 : B v v = 0 := hv' v hv
    by_contra hne
    have := hpos v hne
    rw [h0] at this
    simp at this
  · intro v
    obtain ⟨K, hKo, hKc, hKU⟩ := hbasis {g | ρ g v = v} ((hs v).mem_nhds (by simp))
    have hmap : (fixed W.toRepresentation K).map W.toSubmodule.subtype = W.toSubmodule ⊓ fixed ρ K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∈ fixed W.toRepresentation K := hy
        refine ⟨y.2, ?_⟩
        show (y : V) ∈ fixed ρ K
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff] at hy' ⊢
        intro k hk
        have := congrArg Subtype.val (hy' k hk)
        exact this
      · rintro ⟨hxW, hx⟩
        have hx' : x ∈ fixed ρ K := hx
        refine ⟨⟨x, hxW⟩, ?_, rfl⟩
        show (⟨x, hxW⟩ : W.toSubmodule) ∈ fixed W.toRepresentation K
        rw [GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff] at hx' ⊢
        intro k hk
        apply Subtype.ext
        exact hx' k hk
    have hfd0 : FiniteDimensional ℂ (fixed W.toRepresentation K) := hW.2 K hKo hKc
    have hfd : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V) := by
      rw [← hmap]
      infer_instance
    obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).mpr hfd
    obtain ⟨w, hw, hperp⟩ := GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset B hpos t v
    rw [ht] at hw hperp
    refine ⟨w, hw.1, ?_⟩
    show ∀ x ∈ W.toSubmodule, B (v - w) x = 0
    intro x hx
    refine GlobalTheory.CompanionTheory.UnitSemisimple.orthogonal_of_fixed ρ B hinv K hKc W (v - w) ?_ hperp x hx (hs x)
    intro k hk
    have hv : ρ k v = v := hKU hk
    have hw' : ρ k w = w := (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K w).mp hw.2 k hk
    simp [map_sub, hv, hw']

/- English proof (translation)
Establish `hGL` using `hBZ k`. Establish `hnz : ∀ A : Subrepresentation π, A ≠ ⊥ → ∃ v, v ∈ A.toSubmodule ∧ v ≠ 0`. Introduce `A hA`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hA` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises. Use `show A.toSubmodule = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`. Conclude with `hcon`.

Establish `key : ∀ A : Subrepresentation π, IsAtom A → A = ⊤`. Introduce `A hA`. Assume the negation of the conclusion as `hAt`. Establish `hAirr : A.toRepresentation.IsIrreducible` using `GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom A hA`. Establish `hAs : IsSmooth A.toRepresentation`.

Introduce `v`. Establish `hset : {g | A.toRepresentation g v = v} = {g | π g v = v}`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq]`. Conclude with `Subtype.ext_iff`.

Rewrite using `[hset]`. Conclude with `hs v`. Establish `hAad : IsAdmissible A.toRepresentation` using `hGL.1 (Fin N) _ A.toRepresentation hAs hAirr`. Take `⟨A', hdis, hcod⟩` from `exists_compl_of_admissible π (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N) hs hun A hAad`. Establish `hc : IsCompl A'.toSubmodule A.toSubmodule`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx' hx`. Conclude with `hdis x hx hx'`. Rewrite using `[Submodule.codisjoint_iff_exists_add_eq]`.

Introduce `z`. Take `⟨w, hw, hzw⟩` from `hcod z`. Conclude with `⟨z - w, w, hzw, hw, by abel⟩`. Set `P` to `A'.toSubmodule.projectionOnto A.toSubmodule hc`. Establish `hPv : ∀ v w, w ∈ A.toSubmodule → (hm : v - w ∈ A'.toSubmodule) → P v = ⟨v - w, hm⟩`.

Introduce `v w hw hm`. Establish `hv : v = w + (v - w)` using `by abel`. Establish `h0 : P w = 0` using `Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩`. Establish `h1 : P (v - w) = ⟨v - w, hm⟩` using `Submodule.linearProjOfIsCompl_apply_left hc ⟨v - w, hm⟩`. Use `conv_lhs => rw [hv]`.

Rewrite using `[map_add, h0, zero_add, h1]`. Establish `hPeq : ∀ g v, P (π g v) = A'.toRepresentation g (P v)`. Introduce `g v`. Take `⟨w, hw, hzw⟩` from `hcod v`. Establish `hm2 : π g v - π g w ∈ A'.toSubmodule`.

Rewrite using `[← map_sub]`. Conclude with `A'.apply_mem_toSubmodule g hzw`. Rewrite using `[hPv v w hw hzw, hPv (π g v) (π g w) (A.apply_mem_toSubmodule g hw) hm2]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show π g v - π g w = π g (v - w)`.

Rewrite using `[map_sub]`. Set `p : π.IntertwiningMap A'.toRepresentation` to `⟨P, fun g => LinearMap.ext fun v => hPeq g v⟩`. Set `ι : A.toRepresentation.IntertwiningMap π` to `⟨A.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩`. Establish `hsurj : Function.Surjective p`. Introduce `y`.

Conclude with `⟨y, Submodule.linearProjOfIsCompl_apply_left hc y⟩`. Establish `hexact : Function.Exact ι p`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hy' : y ∈ A.toSubmodule` using `(Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).mp hy`. Conclude with `⟨⟨y, hy'⟩, rfl⟩`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `Submodule.linearProjOfIsCompl_apply_right hc z`. Establish `hex` using `GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact e hρ ι p hs Subtype.val_injective hsurj hexact`.

Take `⟨a, haA, ha0⟩` from `hnz A hA.1`. Establish `hA1` using `hone A a haA ha0`. Establish `hnt : ∃ v, v ∉ A.toSubmodule`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hAt` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises. Use `show A.toSubmodule = ⊤`. Rewrite using `[Submodule.eq_top_iff']`. Conclude with `hcon`.

Take `⟨v, hv⟩` from `hnt`. Take `⟨w, hw, hzw⟩` from `hcod v`. Establish `hvw : v - w ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises.

Rewrite `h0` using `[sub_eq_zero]`. Rewrite using `[h0]`. Conclude with `hw`. Establish `hA2` using `hone A' (v - w) hzw hvw`. Establish `h2 : 1 + 1 ≤ jhMult ρ (jac e π)`.

Rewrite using `[hex]`. Conclude with `add_le_add hA1 hA2`. Establish `h3` using `h2.trans hjm`. Evaluate the numerical expressions using `at h3`. Establish `hwf` using `((hasFiniteLength_iff_wellFounded π).mp hfl).2`.

Use `haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt hwf.wf`. Use `haveI : Nontrivial (Subrepresentation π) := by`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Use `⟨⟨⊥, ⊤, ?_⟩⟩` and prove the remaining obligations. Introduce `h`.

Establish `h'` using `congrArg Subrepresentation.toSubmodule h`. Establish `hmem : v ∈ (⊤ : Subrepresentation π).toSubmodule` using `Submodule.mem_top`. Rewrite `hmem` using `[← h']`. Conclude with `hv ((Submodule.mem_bot ℂ).mp hmem)`. Use `⟨fun T => ?_⟩` and prove the remaining obligations.

Break down `eq_bot_or_exists_atom_le T with hT | ⟨A, hA, hAT⟩` into its components or cases. Conclude with `Or.inl hT`. Use `right`. Rewrite `hAT` using `[key A hA]`. Conclude with `top_le_iff.mp hAT`.
-/
private theorem isIrreducible_of_occurs (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s N : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hs : IsSmooth π) (hfl : HasFiniteLength π)
    (hun : IsUnitarisable π)
    (hone : ∀ (T : Subrepresentation π) (v : V), v ∈ T.toSubmodule → v ≠ 0 →
      1 ≤ jhMult ρ (jac e T.toRepresentation))
    (hjm : jhMult ρ (jac e π) ≤ 1) : π.IsIrreducible := by
  have hGL := hBZ k
  have hnz : ∀ A : Subrepresentation π, A ≠ ⊥ → ∃ v, v ∈ A.toSubmodule ∧ v ≠ 0 := by
    intro A hA
    by_contra hcon
    push_neg at hcon
    apply hA
    apply Subrepresentation.ext
    show A.toSubmodule = ⊥
    rw [Submodule.eq_bot_iff]
    exact hcon
  have key : ∀ A : Subrepresentation π, IsAtom A → A = ⊤ := by
    intro A hA
    by_contra hAt
    have hAirr : A.toRepresentation.IsIrreducible :=
      GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom A hA
    have hAs : IsSmooth A.toRepresentation := by
      intro v
      have hset : {g | A.toRepresentation g v = v} = {g | π g v = v} := by
        ext g
        simp only [Set.mem_setOf_eq]
        exact Subtype.ext_iff
      rw [hset]
      exact hs v
    have hAad : IsAdmissible A.toRepresentation := hGL.1 (Fin N) _ A.toRepresentation hAs hAirr
    obtain ⟨A', hdis, hcod⟩ := exists_compl_of_admissible π
      (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N) hs hun A hAad
    have hc : IsCompl A'.toSubmodule A.toSubmodule := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx' hx
        exact hdis x hx hx'
      · rw [Submodule.codisjoint_iff_exists_add_eq]
        intro z
        obtain ⟨w, hw, hzw⟩ := hcod z
        exact ⟨z - w, w, hzw, hw, by abel⟩
    let P := A'.toSubmodule.projectionOnto A.toSubmodule hc
    have hPv : ∀ v w, w ∈ A.toSubmodule → (hm : v - w ∈ A'.toSubmodule) → P v = ⟨v - w, hm⟩ := by
      intro v w hw hm
      have hv : v = w + (v - w) := by abel
      have h0 : P w = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
      have h1 : P (v - w) = ⟨v - w, hm⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨v - w, hm⟩
      conv_lhs => rw [hv]
      rw [map_add, h0, zero_add, h1]
    have hPeq : ∀ g v, P (π g v) = A'.toRepresentation g (P v) := by
      intro g v
      obtain ⟨w, hw, hzw⟩ := hcod v
      have hm2 : π g v - π g w ∈ A'.toSubmodule := by
        rw [← map_sub]
        exact A'.apply_mem_toSubmodule g hzw
      rw [hPv v w hw hzw, hPv (π g v) (π g w) (A.apply_mem_toSubmodule g hw) hm2]
      apply Subtype.ext
      show π g v - π g w = π g (v - w)
      rw [map_sub]
    let p : π.IntertwiningMap A'.toRepresentation := ⟨P, fun g => LinearMap.ext fun v => hPeq g v⟩
    let ι : A.toRepresentation.IntertwiningMap π := ⟨A.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
    have hsurj : Function.Surjective p := by
      intro y
      exact ⟨y, Submodule.linearProjOfIsCompl_apply_left hc y⟩
    have hexact : Function.Exact ι p := by
      intro y
      constructor
      · intro hy
        have hy' : y ∈ A.toSubmodule := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).mp hy
        exact ⟨⟨y, hy'⟩, rfl⟩
      · rintro ⟨z, rfl⟩
        exact Submodule.linearProjOfIsCompl_apply_right hc z
    have hex := GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact e hρ ι p hs Subtype.val_injective hsurj hexact
    obtain ⟨a, haA, ha0⟩ := hnz A hA.1
    have hA1 := hone A a haA ha0
    have hnt : ∃ v, v ∉ A.toSubmodule := by
      by_contra hcon
      push_neg at hcon
      apply hAt
      apply Subrepresentation.ext
      show A.toSubmodule = ⊤
      rw [Submodule.eq_top_iff']
      exact hcon
    obtain ⟨v, hv⟩ := hnt
    obtain ⟨w, hw, hzw⟩ := hcod v
    have hvw : v - w ≠ 0 := by
      intro h0
      apply hv
      rw [sub_eq_zero] at h0
      rw [h0]
      exact hw
    have hA2 := hone A' (v - w) hzw hvw
    have h2 : 1 + 1 ≤ jhMult ρ (jac e π) := by
      rw [hex]
      exact add_le_add hA1 hA2
    have h3 := h2.trans hjm
    norm_num at h3
  have hwf := ((hasFiniteLength_iff_wellFounded π).mp hfl).2
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt hwf.wf
  haveI : Nontrivial (Subrepresentation π) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    have hmem : v ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h'] at hmem
    exact hv ((Submodule.mem_bot ℂ).mp hmem)
  refine ⟨fun T => ?_⟩
  rcases eq_bot_or_exists_atom_le T with hT | ⟨A, hA, hAT⟩
  · exact Or.inl hT
  · right
    rw [key A hA] at hAT
    exact top_le_iff.mp hAT

/- English proof (translation)
Use `haveI := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp e hρ hsρ`. Use `isIrreducible_of_occurs hBZ e hρ (parInd e ρ) (isSmooth_parInd _ _) ((hBZ k).2.2.1 _ _ _ e _ ρ hsρ (hasFiniteLength_of_isIrreducible hρ)) hun (fun T v hv hv0 => ?_) hjm` and prove the remaining obligations. Set `ιT : T.toRepresentation.IntertwiningMap (parInd e ρ)` to `⟨T.toSubmodule.subtype, fun _ => rfl⟩`. Conclude with `GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac e hρ ιT ⟨⟨v, hv⟩, hv0⟩`.
-/
private theorem isIrreducible_parInd (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s N : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) {X : Type} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ)
    (hun : IsUnitarisable (parInd e ρ)) (hjm : jhMult ρ (jac e (parInd e ρ)) ≤ 1) :
    (parInd e ρ).IsIrreducible := by
  haveI := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp e hρ hsρ
  refine isIrreducible_of_occurs hBZ e hρ (parInd e ρ) (isSmooth_parInd _ _)
    ((hBZ k).2.2.1 _ _ _ e _ ρ hsρ (hasFiniteLength_of_isIrreducible hρ)) hun (fun T v hv hv0 => ?_) hjm
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  exact GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac e hρ ιT ⟨⟨v, hv⟩, hv0⟩

/- English proof (translation)
Introduce `hBZ k _ _ _ _ x y N hd hx hy hjm`. Establish `hρ : (piTensor fun a => (![x, y] a).rep).IsIrreducible` using `GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor (fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π) ![x, y]`. Establish `hsρ : IsSmooth (piTensor fun a => (![x, y] a).rep)` using `isSmooth_piTensor fun a => (![x, y] a).2.rep.smooth`. Establish `hu : ∀ a, IsUnitarisable (![x, y] a).rep` using `fun a => by fin_cases a`. Conclude with `hx`.

Conclude with `hy`. Conclude with `isIrreducible_parInd hBZ _ hρ hsρ (GlobalTheory.SmGL.UnitInd.isUnitarisable_multiProd _ hu) hjm`.
-/
theorem UpperTheory.Lit.Mix.ss :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), IsUnitarisable x.rep → IsUnitarisable y.rep → jm ![x, y] hd (prodIrr ![x, y] hd) ≤ 1 → (prodIrr ![x, y] hd).IsIrreducible := by
  intro hBZ k _ _ _ _ x y N hd hx hy hjm
  have hρ : (piTensor fun a => (![x, y] a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor (fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π) ![x, y]
  have hsρ : IsSmooth (piTensor fun a => (![x, y] a).rep) := isSmooth_piTensor fun a => (![x, y] a).2.rep.smooth
  have hu : ∀ a, IsUnitarisable (![x, y] a).rep := fun a => by
    fin_cases a
    · exact hx
    · exact hy
  exact isIrreducible_parInd hBZ _ hρ hsρ (GlobalTheory.SmGL.UnitInd.isUnitarisable_multiProd _ hu) hjm
