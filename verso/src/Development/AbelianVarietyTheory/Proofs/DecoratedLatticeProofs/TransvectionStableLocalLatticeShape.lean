import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ i L c hcard hc hcl hbd hex`. Take `⟨x₀, hx₀, j, hj⟩` from `hex`. Choose the witnesses or unpack the hypotheses as in `⟨a, hai, haj⟩ : ∃ a, a ≠ i ∧ a ≠ j := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Establish `hsub : (Finset.univ : Finset n) ⊆ {i, j}` using `fun b _ => by`. Distinguish the cases in `hbi : b = i`. Simplify using `[hbi]`. Simplify using `[h b hbi]`. Establish `h1` using `Finset.card_le_card hsub`.

Establish `h2 : ({i, j} : Finset n).card ≤ 2` using `Finset.card_le_two`. Rewrite `h1` using `[Finset.card_univ]`. Use linear arithmetic over natural numbers and integers. Establish `hsm : ∀ (s : 𝒪[k]) (b : n) (y : k), (s • (Pi.single b y : n → k) : n → k) = (Pi.single b ((s : k) * y) : n → k)`. Introduce `s b y`.

Use extensionality with `m`. Distinguish the cases in `hm : m = b`. Substitute `hm` using the available equality. Simplify using `[Subring.smul_def]`. Simplify using `[hm, Subring.smul_def]`.

Establish `ha : ∀ t : 𝒪[k], Pi.single a ((t : k) * c) ∈ L`. Introduce `t`. Establish `h` using `L.sub_mem (hcl x₀ hx₀ a j t haj (Or.inl hai)) hx₀`. Simplify `h` using `[hj]`. Establish `hca : Pi.single a c ∈ L` using `by simpa using ha 1`.

Establish `hsing : ∀ b, b ≠ i → ∀ t : 𝒪[k], Pi.single b ((t : k) * c) ∈ L`. Introduce `b hbi t`. Distinguish the cases in `hba : b = a`. Substitute `hba` using the available equality. Conclude with `ha t`.

Establish `h` using `L.sub_mem (hcl (Pi.single a c) hca b a t hba (Or.inl hbi)) hca`. Simplify using `using h`. Establish `hi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → Pi.single i ((t : k) * c) ∈ L`. Introduce `t ht`. Establish `h` using `L.sub_mem (hcl (Pi.single a c) hca i a t (Ne.symm hai) (Or.inr ht)) hca`.

Simplify `h` using `[Ne.symm hai]`. Establish `hsum : ∀ x : n → k, (∀ b, Pi.single b (x b) ∈ L) → x ∈ L`. Introduce `x h`. Rewrite using `[← Finset.univ_sum_single x]`. Conclude with `L.sum_mem (fun b _ => h b)`.

Establish `hoff : ∀ x : n → k, (∀ j, c⁻¹ * x j ∈ 𝒪[k]) → ∀ b, b ≠ i → Pi.single b (x b) ∈ L`. Introduce `x hx b hb`. Establish `e : x b = (c⁻¹ * x b) * c` using `by field_simp`. Rewrite using `[e]`. Conclude with `hsing b hb ⟨_, hx b⟩`.

Distinguish the cases in `hci : Pi.single i c ∈ L`. Use `left`. Introduce `x`. Use `⟨hbd x, fun hx => hsum x fun b => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : b = i`.

Substitute `hb` using the available equality. Establish `e : Pi.single b (x b) = ((⟨c⁻¹ * x b, hx b⟩ : 𝒪[k]) • (Pi.single b c : n → k) : n → k)`. Rewrite using `[hsm]`. Use `congr 1`. Use `show x b = (c⁻¹ * x b) * c`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `L.smul_mem _ hci`. Conclude with `hoff x hx b hb`. Use `right`.

Establish `hm : ∀ x (hx : x ∈ L), (⟨c⁻¹ * x i, hbd x hx i⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k]`. Introduce `x hx`. Assume the negation of the conclusion as `hu`. Rewrite `hu` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Take `⟨v, hv⟩` from `hu`.

Establish `hy : x - Pi.single i (x i) ∈ L`. Apply `hsum` to reduce the goal to its premises. Introduce `b`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality.

Simplify using the standard rewrite rules. Use `hoff x (hbd x hx) b hb` as an intermediate fact. Simplify `this` using `[hb]`. Establish `hxi : Pi.single i (x i) ∈ L`. Use `L.sub_mem hx hy` as an intermediate fact.

Simplify using `using this`. Apply `hci` to reduce the goal to its premises. Establish `h1 : ((↑(v⁻¹) : 𝒪[k]) * (v : 𝒪[k])) = 1` using `Units.inv_mul v`. Rewrite `h1` using `[hv]`. Establish `h2` using `congrArg (fun z : 𝒪[k] => (z : k)) h1`.

Simplify using `only [Subring.coe_mul, OneMemClass.coe_one] at h2`. Use `set w : k := ((↑(v⁻¹) : 𝒪[k]) : k)`. Establish `hcc : c * c⁻¹ = 1` using `mul_inv_cancel₀ hc`. Establish `e : Pi.single i c = ((↑(v⁻¹) : 𝒪[k]) • (Pi.single i (x i) : n → k) : n → k)`. Rewrite using `[hsm]`.

Use `congr 1`. Use `show c = w * x i`. Take the linear combination `-(c * h2) + (w * x i) * hcc`. Rewrite using `[e]`. Conclude with `L.smul_mem _ hxi`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨hbd x hx, ⟨c⁻¹ * x i, hbd x hx i⟩, hm x hx, rfl⟩`. Introduce and unpack `⟨hx, s, hs, hsx⟩`.

Use `hsum x fun b => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality. Establish `e : x b = (s : k) * c` using `by rw [hsx]; field_simp`. Rewrite using `[e]`.

Conclude with `hi s hs`. Conclude with `hoff x hx b hb`.
-/
theorem GlobalTheory.LatPairStab.stable_lattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  intro k _ _ _ _ n _ _ i L c hcard hc hcl hbd hex
  obtain ⟨x₀, hx₀, j, hj⟩ := hex
  obtain ⟨a, hai, haj⟩ : ∃ a, a ≠ i ∧ a ≠ j := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset n) ⊆ {i, j} := fun b _ => by
      by_cases hbi : b = i
      · simp [hbi]
      · simp [h b hbi]
    have h1 := Finset.card_le_card hsub
    have h2 : ({i, j} : Finset n).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at h1
    omega

  have hsm : ∀ (s : 𝒪[k]) (b : n) (y : k), (s • (Pi.single b y : n → k) : n → k) = (Pi.single b ((s : k) * y) : n → k) := by
    intro s b y
    ext m
    by_cases hm : m = b
    · subst hm; simp [Subring.smul_def]
    · simp [hm, Subring.smul_def]

  have ha : ∀ t : 𝒪[k], Pi.single a ((t : k) * c) ∈ L := by
    intro t
    have h := L.sub_mem (hcl x₀ hx₀ a j t haj (Or.inl hai)) hx₀
    simpa [hj] using h
  have hca : Pi.single a c ∈ L := by simpa using ha 1

  have hsing : ∀ b, b ≠ i → ∀ t : 𝒪[k], Pi.single b ((t : k) * c) ∈ L := by
    intro b hbi t
    by_cases hba : b = a
    · subst hba; exact ha t
    · have h := L.sub_mem (hcl (Pi.single a c) hca b a t hba (Or.inl hbi)) hca
      simpa using h

  have hi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → Pi.single i ((t : k) * c) ∈ L := by
    intro t ht
    have h := L.sub_mem (hcl (Pi.single a c) hca i a t (Ne.symm hai) (Or.inr ht)) hca
    simpa [Ne.symm hai] using h

  have hsum : ∀ x : n → k, (∀ b, Pi.single b (x b) ∈ L) → x ∈ L := by
    intro x h
    rw [← Finset.univ_sum_single x]
    exact L.sum_mem (fun b _ => h b)
  have hoff : ∀ x : n → k, (∀ j, c⁻¹ * x j ∈ 𝒪[k]) → ∀ b, b ≠ i → Pi.single b (x b) ∈ L := by
    intro x hx b hb
    have e : x b = (c⁻¹ * x b) * c := by field_simp
    rw [e]
    exact hsing b hb ⟨_, hx b⟩
  by_cases hci : Pi.single i c ∈ L
  · left
    intro x
    refine ⟨hbd x, fun hx => hsum x fun b => ?_⟩
    by_cases hb : b = i
    · subst hb
      have e : Pi.single b (x b) = ((⟨c⁻¹ * x b, hx b⟩ : 𝒪[k]) • (Pi.single b c : n → k) : n → k) := by
        rw [hsm]; congr 1; show x b = (c⁻¹ * x b) * c; field_simp
      rw [e]; exact L.smul_mem _ hci
    · exact hoff x hx b hb
  · right
    have hm : ∀ x (hx : x ∈ L), (⟨c⁻¹ * x i, hbd x hx i⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      intro x hx
      by_contra hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
      obtain ⟨v, hv⟩ := hu

      have hy : x - Pi.single i (x i) ∈ L := by
        apply hsum
        intro b
        by_cases hb : b = i
        · subst hb; simp
        · have := hoff x (hbd x hx) b hb
          simpa [hb] using this
      have hxi : Pi.single i (x i) ∈ L := by
        have := L.sub_mem hx hy
        simpa using this
      apply hci
      have h1 : ((↑(v⁻¹) : 𝒪[k]) * (v : 𝒪[k])) = 1 := Units.inv_mul v
      rw [hv] at h1
      have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
      simp only [Subring.coe_mul, OneMemClass.coe_one] at h2
      set w : k := ((↑(v⁻¹) : 𝒪[k]) : k)
      have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
      have e : Pi.single i c = ((↑(v⁻¹) : 𝒪[k]) • (Pi.single i (x i) : n → k) : n → k) := by
        rw [hsm]; congr 1
        show c = w * x i
        linear_combination -(c * h2) + (w * x i) * hcc
      rw [e]; exact L.smul_mem _ hxi
    intro x
    constructor
    · intro hx
      exact ⟨hbd x hx, ⟨c⁻¹ * x i, hbd x hx i⟩, hm x hx, rfl⟩
    · rintro ⟨hx, s, hs, hsx⟩
      refine hsum x fun b => ?_
      by_cases hb : b = i
      · subst hb
        have e : x b = (s : k) * c := by rw [hsx]; field_simp
        rw [e]; exact hi s hs
      · exact hoff x hx b hb
