import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace P_exGrp

/- English proof (translation)
Establish `hopen : IsOpen (μ.ker : Set kˣ)` using `hμ`. Take `⟨V, hVo, hV⟩` from `(Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen`. Establish `h1 : (1 : k) ∈ V`. Establish `: (1 : kˣ) ∈ (Units.val ⁻¹' V)` using `by rw [hV]; exact μ.ker.one_mem`. Simplify using `using this`.

Take `⟨γ, hγ⟩` from `(IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[k]`. Establish `hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1` using `(Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ`. Establish `: MulArchimedean (ValueGroupWithZero k)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Take `⟨c, hc⟩` from `exists_pow_lt₀ hlt γ`.

Use `⟨c, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Rewrite `hu` using `[hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨t, ht⟩` from `hu`. Establish `e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t`.

Use `congrArg (algebraMap 𝒪[k] k) ht` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, map_mul, map_pow]`. Conclude with `this`. Establish `ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1` using `t.2`. Establish `hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ`.

Rewrite using `[e, map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmem : ((u : 𝒪[k]) : k) ∈ V` using `hγ hv`. Establish `hk : unitIncl k u ∈ μ.ker`. Establish `: unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ)` using `hmem`.

Rewrite `this` using `[hV]`. Conclude with `this`. Conclude with `hk`.
-/
theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1 := by
  have hopen : IsOpen (μ.ker : Set kˣ) := hμ
  obtain ⟨V, hVo, hV⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' V) := by rw [hV]; exact μ.ker.one_mem
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1 :=
    (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hlt γ
  refine ⟨c, fun u hu => ?_⟩
  have hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht⟩ := hu
  have e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t := by
    have := congrArg (algebraMap 𝒪[k] k) ht
    rw [map_sub, map_one, map_mul, map_pow] at this
    exact this
  have ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1 := t.2
  have hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ := by
    rw [e, map_mul, map_pow]
    calc valuation k (algebraMap 𝒪[k] k ϖ) ^ c * valuation k (algebraMap 𝒪[k] k t)
        ≤ valuation k (algebraMap 𝒪[k] k ϖ) ^ c := mul_le_of_le_one_right' ht1
      _ < γ := hc
  have hmem : ((u : 𝒪[k]) : k) ∈ V := hγ hv
  have hk : unitIncl k u ∈ μ.ker := by
    have : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ) := hmem
    rw [hV] at this
    exact this
  exact hk

def Good {α : Type} (d : α → α → ℕ) (l : List α) : Prop :=
  ∀ (a a' b' b : ℕ) (h1 : a ≤ a') (h2 : a' < b') (h3 : b' ≤ b) (hb : b < l.length),
    d (l[a']'(by omega)) (l[b']'(by omega)) ≤ d (l[a]'(by omega)) (l[b])

/- English proof (translation)
Proceed by induction on `S using Finset.strongInduction with`. Consider the case `H S ih`. Introduce `h0 hs hu`. Use `set r : ℕ := (S ×ˢ S).sup (fun p => d p.1 p.2) with hr`. Establish `hle : ∀ x ∈ S, ∀ y ∈ S, d x y ≤ r` using `fun x hx y hy => Finset.le_sup (f := fun p : α × α => d p.1 p.2) (b := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)`.

Distinguish the cases in `hr0 : r = 0`. Use `⟨S.toList, Finset.nodup_toList S, fun x => Finset.mem_toList, ?_⟩` and prove the remaining obligations. Introduce `a a' b' b h1 h2 h3 hb`. Use `hle (S.toList[a']'(by omega)) (Finset.mem_toList.mp (List.getElem_mem _)) (S.toList[b']'(by omega)) (Finset.mem_toList.mp (List.getElem_mem _))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hSne : S.Nonempty`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Finset.not_nonempty_iff_eq_empty]`. Apply `hr0` to reduce the goal to its premises. Rewrite using `[hr, hne]`.

Simplify using the standard rewrite rules. Take `⟨x, hx⟩` from `hSne`. Take `⟨p, hp, hpr⟩` from `Finset.exists_mem_eq_sup (S ×ˢ S) ⟨(x, x), Finset.mem_product.mpr ⟨hx, hx⟩⟩ (fun p : α × α => d p.1 p.2)`. Rewrite `hpr` using `[← hr]`. Take `⟨hp1, hp2⟩` from `Finset.mem_product.mp hp`.

Use `set A := S.filter (fun y => d x y < r) with hA`. Use `set B := S.filter (fun y => ¬ d x y < r) with hB`. Establish `hAS : A ⊂ S`. Rewrite using `[hA, Finset.filter_ssubset]`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Establish `h1` using `hu p.1 hp1 x hx p.2 hp2`. Rewrite `h1` using `[hs p.1 hp1 x hx]`. Establish `h2` using `hall p.1 hp1`. Establish `h3` using `hall p.2 hp2`.

Establish `: max (d x p.1) (d x p.2) < r` using `max_lt h2 h3`. Use linear arithmetic over natural numbers and integers. Establish `hBS : B ⊂ S`. Rewrite using `[hB, Finset.filter_ssubset]`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[h0 x hx]`. Use `push Not`. Use linear arithmetic over natural numbers and integers. Establish `memA : ∀ y, y ∈ A ↔ y ∈ S ∧ d x y < r` using `fun y => Finset.mem_filter`. Establish `memB : ∀ y, y ∈ B ↔ y ∈ S ∧ ¬ d x y < r` using `fun y => Finset.mem_filter`.

Take `⟨lA, nA, mA, gA⟩` from `ih A hAS (fun y hy => h0 y ((memA y).mp hy).1) (fun y hy z hz => hs y ((memA y).mp hy).1 z ((memA z).mp hz).1) (fun y hy z hz w hw => hu y ((memA y).mp hy).1 z ((memA z).mp hz).1 w ((memA w).mp hw).1)`. Take `⟨lB, nB, mB, gB⟩` from `ih B hBS (fun y hy => h0 y ((memB y).mp hy).1) (fun y hy z hz => hs y ((memB y).mp hy).1 z ((memB z).mp hz).1) (fun y hy z hz w hw => hu y ((memB y).mp hy).1 z ((memB z).mp hz).1 w ((memB w).mp hw).1)`. Establish `hmem : ∀ y, y ∈ lA ++ lB ↔ y ∈ S`. Introduce `y`. Rewrite using `[List.mem_append, mA, mB, memA, memB]`.

The claim follows by propositional logic. Use `⟨lA ++ lB, ?_, hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[List.nodup_append]`. Use `⟨nA, nB, ?_⟩` and prove the remaining obligations. Introduce `y hy z hz hyz`.

Substitute `hyz` using the available equality. Conclude with `((memB y).mp ((mB y).mp hz)).2 ((memA y).mp ((mA y).mp hy)).2`. Introduce `a a' b' b h1 h2 h3 hb`. Establish `hlen : (lA ++ lB).length = lA.length + lB.length` using `List.length_append`. Establish `eL : ∀ i (hi : i < lA.length) (h : i < (lA ++ lB).length), (lA ++ lB)[i] = lA[i]` using `fun i hi h => List.getElem_append_left hi`.

Establish `eR : ∀ i (hi : lA.length ≤ i) (h : i < (lA ++ lB).length), (lA ++ lB)[i] = lB[i - lA.length]'(by omega)` using `fun i hi h => List.getElem_append_right hi`. Establish `inS : ∀ i (h : i < (lA ++ lB).length), (lA ++ lB)[i] ∈ S` using `fun i h => (hmem _).mp (List.getElem_mem _)`. Distinguish the cases in `hbA : b < lA.length`. Rewrite using `[eL a (by omega), eL a' (by omega), eL b' (by omega), eL b hbA]`. Conclude with `gA a a' b' b h1 h2 h3 hbA`.

Distinguish the cases in `haA : lA.length ≤ a`. Rewrite using `[eR a haA, eR a' (by omega), eR b' (by omega), eR b (by omega)]`. Conclude with `gB (a - lA.length) (a' - lA.length) (b' - lA.length) (b - lA.length) (by omega) (by omega) (by omega) (by omega)`. Use `push Not at hbA haA`. Establish `hxa : d x (lA ++ lB)[a] < r`.

Rewrite using `[eL a haA]`. Conclude with `((memA _).mp ((mA _).mp (List.getElem_mem _))).2`. Establish `hxb : ¬ d x (lA ++ lB)[b] < r`. Rewrite using `[eR b hbA]`. Conclude with `((memB _).mp ((mB _).mp (List.getElem_mem _))).2`.

Establish `hab : r ≤ d (lA ++ lB)[a] (lA ++ lB)[b]`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Use `hu x hx _ (inS a (by omega)) _ (inS b hb)` as an intermediate fact. Establish `: max (d x (lA ++ lB)[a]) (d (lA ++ lB)[a] (lA ++ lB)[b]) < r` using `max_lt hxa hlt`.

Use linear arithmetic over natural numbers and integers. Conclude with `le_trans (hle _ (inS a' (by omega)) _ (inS b' (by omega))) hab`.
-/
theorem exists_idempotent_mul_natPow_of_mul {α : Type} (d : α → α → ℕ) (S : Finset α) :
    (∀ x ∈ S, d x x = 0) → (∀ x ∈ S, ∀ y ∈ S, d x y = d y x) →
    (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, d x z ≤ max (d x y) (d y z)) →
    ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ S) ∧ Good d l := by
  induction S using Finset.strongInduction with
  | H S ih =>
  intro h0 hs hu
  set r : ℕ := (S ×ˢ S).sup (fun p => d p.1 p.2) with hr
  have hle : ∀ x ∈ S, ∀ y ∈ S, d x y ≤ r := fun x hx y hy =>
    Finset.le_sup (f := fun p : α × α => d p.1 p.2) (b := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩)
  by_cases hr0 : r = 0
  · refine ⟨S.toList, Finset.nodup_toList S, fun x => Finset.mem_toList, ?_⟩
    intro a a' b' b h1 h2 h3 hb
    have := hle (S.toList[a']'(by omega)) (Finset.mem_toList.mp (List.getElem_mem _))
      (S.toList[b']'(by omega)) (Finset.mem_toList.mp (List.getElem_mem _))
    omega
  · have hSne : S.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply hr0
      rw [hr, hne]
      simp
    obtain ⟨x, hx⟩ := hSne
    obtain ⟨p, hp, hpr⟩ := Finset.exists_mem_eq_sup (S ×ˢ S) ⟨(x, x), Finset.mem_product.mpr ⟨hx, hx⟩⟩
      (fun p : α × α => d p.1 p.2)
    rw [← hr] at hpr
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    set A := S.filter (fun y => d x y < r) with hA
    set B := S.filter (fun y => ¬ d x y < r) with hB
    have hAS : A ⊂ S := by
      rw [hA, Finset.filter_ssubset]
      by_contra hall
      push Not at hall
      have h1 := hu p.1 hp1 x hx p.2 hp2
      rw [hs p.1 hp1 x hx] at h1
      have h2 := hall p.1 hp1
      have h3 := hall p.2 hp2
      have : max (d x p.1) (d x p.2) < r := max_lt h2 h3
      omega
    have hBS : B ⊂ S := by
      rw [hB, Finset.filter_ssubset]
      refine ⟨x, hx, ?_⟩
      rw [h0 x hx]
      push Not
      omega
    have memA : ∀ y, y ∈ A ↔ y ∈ S ∧ d x y < r := fun y => Finset.mem_filter
    have memB : ∀ y, y ∈ B ↔ y ∈ S ∧ ¬ d x y < r := fun y => Finset.mem_filter
    obtain ⟨lA, nA, mA, gA⟩ := ih A hAS (fun y hy => h0 y ((memA y).mp hy).1)
      (fun y hy z hz => hs y ((memA y).mp hy).1 z ((memA z).mp hz).1)
      (fun y hy z hz w hw => hu y ((memA y).mp hy).1 z ((memA z).mp hz).1 w ((memA w).mp hw).1)
    obtain ⟨lB, nB, mB, gB⟩ := ih B hBS (fun y hy => h0 y ((memB y).mp hy).1)
      (fun y hy z hz => hs y ((memB y).mp hy).1 z ((memB z).mp hz).1)
      (fun y hy z hz w hw => hu y ((memB y).mp hy).1 z ((memB z).mp hz).1 w ((memB w).mp hw).1)
    have hmem : ∀ y, y ∈ lA ++ lB ↔ y ∈ S := by
      intro y
      rw [List.mem_append, mA, mB, memA, memB]
      tauto
    refine ⟨lA ++ lB, ?_, hmem, ?_⟩
    · rw [List.nodup_append]
      refine ⟨nA, nB, ?_⟩
      intro y hy z hz hyz
      subst hyz
      exact ((memB y).mp ((mB y).mp hz)).2 ((memA y).mp ((mA y).mp hy)).2
    · intro a a' b' b h1 h2 h3 hb
      have hlen : (lA ++ lB).length = lA.length + lB.length := List.length_append
      have eL : ∀ i (hi : i < lA.length) (h : i < (lA ++ lB).length), (lA ++ lB)[i] = lA[i] :=
        fun i hi h => List.getElem_append_left hi
      have eR : ∀ i (hi : lA.length ≤ i) (h : i < (lA ++ lB).length),
          (lA ++ lB)[i] = lB[i - lA.length]'(by omega) :=
        fun i hi h => List.getElem_append_right hi
      have inS : ∀ i (h : i < (lA ++ lB).length), (lA ++ lB)[i] ∈ S :=
        fun i h => (hmem _).mp (List.getElem_mem _)
      by_cases hbA : b < lA.length
      · rw [eL a (by omega), eL a' (by omega), eL b' (by omega), eL b hbA]
        exact gA a a' b' b h1 h2 h3 hbA
      · by_cases haA : lA.length ≤ a
        · rw [eR a haA, eR a' (by omega), eR b' (by omega), eR b (by omega)]
          exact gB (a - lA.length) (a' - lA.length) (b' - lA.length) (b - lA.length) (by omega) (by omega)
            (by omega) (by omega)
        · push Not at hbA haA
          have hxa : d x (lA ++ lB)[a] < r := by
            rw [eL a haA]
            exact ((memA _).mp ((mA _).mp (List.getElem_mem _))).2
          have hxb : ¬ d x (lA ++ lB)[b] < r := by
            rw [eR b hbA]
            exact ((memB _).mp ((mB _).mp (List.getElem_mem _))).2
          have hab : r ≤ d (lA ++ lB)[a] (lA ++ lB)[b] := by
            by_contra hlt
            push Not at hlt
            have := hu x hx _ (inS a (by omega)) _ (inS b hb)
            have : max (d x (lA ++ lB)[a]) (d (lA ++ lB)[a] (lA ++ lB)[b]) < r := max_lt hxa hlt
            omega
          exact le_trans (hle _ (inS a' (by omega)) _ (inS b' (by omega))) hab

/- English proof (translation)
The claim follows from `exists_idempotent_mul_natPow_of_mul d S h0 hs hu`.
-/
theorem exists_good_list {α : Type} (S : Finset α) (d : α → α → ℕ)
    (h0 : ∀ x ∈ S, d x x = 0) (hs : ∀ x ∈ S, ∀ y ∈ S, d x y = d y x)
    (hu : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, d x z ≤ max (d x y) (d y z)) :
    ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ S) ∧
      ∀ (a a' b' b : ℕ) (h1 : a ≤ a') (h2 : a' < b') (h3 : b' ≤ b) (hb : b < l.length),
        d (l[a']'(by omega)) (l[b']'(by omega)) ≤ d (l[a]'(by omega)) (l[b]) :=
  exists_idempotent_mul_natPow_of_mul d S h0 hs hu

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

/- English proof (translation)
Introduce `u hu` and use `hc u (Ideal.pow_le_pow_right h hu)`.
-/
theorem Lv_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c c' : ℕ} (h : c ≤ c') (hc : c ∈ Lv ψ) : c' ∈ Lv ψ :=
  fun u hu => hc u (Ideal.pow_le_pow_right h hu)

/- English proof (translation)
Apply `Nat.sInf_eq_zero.mpr` to reduce the goal to its premises. Use `left`. Introduce `u _`. Simplify using the standard rewrite rules.
-/
theorem cond_div_self (ψ : 𝒪[k]ˣ →* ℂˣ) : cond (ψ / ψ) = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left
  intro u _
  simp

/- English proof (translation)
Unfold `cond`. Use `congr 1`. Use extensionality with `c`. Simplify using `only [Set.mem_ofPred_eq, MonoidHom.div_apply, div_eq_one]`. Conclude with `forall_congr' fun u => imp_congr_right fun _ => eq_comm`.
-/
theorem cond_div_comm (ψ φ : 𝒪[k]ˣ →* ℂˣ) : cond (ψ / φ) = cond (φ / ψ) := by
  unfold cond
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq, MonoidHom.div_apply, div_eq_one]
  exact forall_congr' fun u => imp_congr_right fun _ => eq_comm

/- English proof (translation)
Take `⟨c1, hc1⟩` from `h1`. Take `⟨c2, hc2⟩` from `h2`. Take `⟨c3, hc3⟩` from `h3`. Establish `hA : cond (ψ / φ) ∈ Lv (ψ / φ)` using `Nat.sInf_mem ⟨max c1 c2, fun u hu => by`. Rewrite using `[MonoidHom.div_apply, Lv_mono ψ (le_max_left _ _) hc1 u hu, Lv_mono φ (le_max_right _ _) hc2 u hu, div_one]⟩`.

Establish `hB : cond (φ / ξ) ∈ Lv (φ / ξ)` using `Nat.sInf_mem ⟨max c2 c3, fun u hu => by`. Rewrite using `[MonoidHom.div_apply, Lv_mono φ (le_max_left _ _) hc2 u hu, Lv_mono ξ (le_max_right _ _) hc3 u hu, div_one]⟩`. Apply `Nat.sInf_le` to reduce the goal to its premises. Introduce `u hu`. Establish `e1` using `Lv_mono _ (le_max_left _ _) hA u hu`.

Establish `e2` using `Lv_mono _ (le_max_right _ _) hB u hu`. Rewrite `e1`, `e2`, the goal using `[MonoidHom.div_apply, div_eq_one]`. Rewrite using `[e1, e2]`.
-/
theorem cond_div_ultra (ψ φ ξ : 𝒪[k]ˣ →* ℂˣ) (h1 : (Lv ψ).Nonempty) (h2 : (Lv φ).Nonempty) (h3 : (Lv ξ).Nonempty) :
    cond (ψ / ξ) ≤ max (cond (ψ / φ)) (cond (φ / ξ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  obtain ⟨c3, hc3⟩ := h3
  have hA : cond (ψ / φ) ∈ Lv (ψ / φ) := Nat.sInf_mem ⟨max c1 c2, fun u hu => by
    rw [MonoidHom.div_apply, Lv_mono ψ (le_max_left _ _) hc1 u hu, Lv_mono φ (le_max_right _ _) hc2 u hu, div_one]⟩
  have hB : cond (φ / ξ) ∈ Lv (φ / ξ) := Nat.sInf_mem ⟨max c2 c3, fun u hu => by
    rw [MonoidHom.div_apply, Lv_mono φ (le_max_left _ _) hc2 u hu, Lv_mono ξ (le_max_right _ _) hc3 u hu, div_one]⟩
  apply Nat.sInf_le
  intro u hu
  have e1 := Lv_mono _ (le_max_left _ _) hA u hu
  have e2 := Lv_mono _ (le_max_right _ _) hB u hu
  rw [MonoidHom.div_apply, div_eq_one] at e1 e2 ⊢
  rw [e1, e2]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use extensionality with `u`. Simplify using `[res, MonoidHom.div_apply]`.
-/
theorem res_div (μ ν : kˣ →* ℂˣ) : res (μ / ν) = res μ / res ν := by
  ext u
  simp [res, MonoidHom.div_apply]

end P_exGrp

open P_exGrp in

/- English proof (translation)
Introduce `n χ hχ`. Set `S : Finset (𝒪[k]ˣ →* ℂˣ)` to `Finset.univ.image (fun i => res (χ i))`. Establish `hLv : ∀ ψ ∈ S, (Lv ψ).Nonempty`. Introduce `ψ hψ`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hψ`.

Conclude with `exists_level (χ i) (hχ i)`. Take `⟨l, hnd, hmem, hgood⟩` from `exists_good_list S (fun ψ φ => cond (ψ / φ)) (fun x _ => cond_div_self x) (fun x _ y _ => cond_div_comm x y) (fun x hx y hy z hz => cond_div_ultra x y z (hLv x hx) (hLv y hy) (hLv z hz))`. Establish `hinS : ∀ i, res (χ i) ∈ l` using `fun i => (hmem _).mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Establish `hex : ∀ i, ∃ a : Fin l.length, l[(a : ℕ)] = res (χ i)`. Introduce `i`.

Take `⟨a, ha, h⟩` from `List.mem_iff_getElem.mp (hinS i)`. Conclude with `⟨⟨a, ha⟩, h⟩`. Set `f : Fin n → Fin l.length` to `fun i => Classical.choose (hex i)`. Establish `hf : ∀ i, l[((f i : Fin l.length) : ℕ)] = res (χ i)` using `fun i => Classical.choose_spec (hex i)`. Establish `hrep : ∀ a : Fin l.length, ∃ i, res (χ i) = l[(a : ℕ)]`.

Introduce `a`. Establish `: l[(a : ℕ)] ∈ S` using `(hmem _).mp (List.getElem_mem _)`. Take `⟨i, -, h⟩` from `Finset.mem_image.mp this`. Conclude with `⟨i, h⟩`. Set `rep : Fin l.length → Fin n` to `fun a => Classical.choose (hrep a)`.

Establish `hrep' : ∀ a, res (χ (rep a)) = l[(a : ℕ)]` using `fun a => Classical.choose_spec (hrep a)`. Establish `hfrep : ∀ a, f (rep a) = a`. Introduce `a`. Apply `Fin.ext` to reduce the goal to its premises. Conclude with `(hnd.getElem_inj_iff).mp ((hf (rep a)).trans (hrep' a))`.

Set `G : Grp k n` to `{ s := l.length d := fun a => Fintype.card {i // f i = a} pos := fun a => Fintype.card_pos_iff.mpr ⟨⟨rep a, hfrep a⟩⟩ hd := by`. Rewrite using `[← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_fin]`. Use `μ := fun a => χ (rep a)`. Use `smooth := fun a => hχ (rep a)`. Use `dist := by`.

Introduce `a b hab h`. Apply `hab` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Rewrite `h` using `[hrep', hrep']`. Conclude with `(hnd.getElem_inj_iff).mp h`.

Use `ball := by`. Introduce `a a' b' b h1 h2 h3`. Unfold `cc`. Rewrite using `[res_div, res_div, hrep', hrep', hrep', hrep']`. Conclude with `hgood a a' b' b h1 h2 h3 b.isLt }`.

Set `τ : (Σ a : Fin G.s, Fin (G.d a)) ≃ Fin n` to `(Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {i // f i = a}).symm)).trans (Equiv.sigmaFiberEquiv f)`. Use `⟨G, G.e.symm.trans τ, fun i => ?_⟩` and prove the remaining obligations. Establish `key : f ((G.e.symm.trans τ) i) = G.bl i` using `((Fintype.equivFin {j // f j = (G.e.symm i).1}).symm (G.e.symm i).2).2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem step_exGrp : ExistsGroupElementProp (k := k) := by
  intro n χ hχ
  let S : Finset (𝒪[k]ˣ →* ℂˣ) := Finset.univ.image (fun i => res (χ i))
  have hLv : ∀ ψ ∈ S, (Lv ψ).Nonempty := by
    intro ψ hψ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hψ
    exact exists_level (χ i) (hχ i)
  obtain ⟨l, hnd, hmem, hgood⟩ := exists_good_list S (fun ψ φ => cond (ψ / φ))
    (fun x _ => cond_div_self x) (fun x _ y _ => cond_div_comm x y)
    (fun x hx y hy z hz => cond_div_ultra x y z (hLv x hx) (hLv y hy) (hLv z hz))
  have hinS : ∀ i, res (χ i) ∈ l := fun i => (hmem _).mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hex : ∀ i, ∃ a : Fin l.length, l[(a : ℕ)] = res (χ i) := by
    intro i
    obtain ⟨a, ha, h⟩ := List.mem_iff_getElem.mp (hinS i)
    exact ⟨⟨a, ha⟩, h⟩
  let f : Fin n → Fin l.length := fun i => Classical.choose (hex i)
  have hf : ∀ i, l[((f i : Fin l.length) : ℕ)] = res (χ i) := fun i => Classical.choose_spec (hex i)
  have hrep : ∀ a : Fin l.length, ∃ i, res (χ i) = l[(a : ℕ)] := by
    intro a
    have : l[(a : ℕ)] ∈ S := (hmem _).mp (List.getElem_mem _)
    obtain ⟨i, -, h⟩ := Finset.mem_image.mp this
    exact ⟨i, h⟩
  let rep : Fin l.length → Fin n := fun a => Classical.choose (hrep a)
  have hrep' : ∀ a, res (χ (rep a)) = l[(a : ℕ)] := fun a => Classical.choose_spec (hrep a)
  have hfrep : ∀ a, f (rep a) = a := by
    intro a
    apply Fin.ext
    exact (hnd.getElem_inj_iff).mp ((hf (rep a)).trans (hrep' a))
  let G : Grp k n :=
    { s := l.length
      d := fun a => Fintype.card {i // f i = a}
      pos := fun a => Fintype.card_pos_iff.mpr ⟨⟨rep a, hfrep a⟩⟩
      hd := by
        rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_fin]
      μ := fun a => χ (rep a)
      smooth := fun a => hχ (rep a)
      dist := by
        intro a b hab h
        apply hab
        apply Fin.ext
        rw [hrep', hrep'] at h
        exact (hnd.getElem_inj_iff).mp h
      ball := by
        intro a a' b' b h1 h2 h3
        unfold cc
        rw [res_div, res_div, hrep', hrep', hrep', hrep']
        exact hgood a a' b' b h1 h2 h3 b.isLt }
  let τ : (Σ a : Fin G.s, Fin (G.d a)) ≃ Fin n :=
    (Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {i // f i = a}).symm)).trans (Equiv.sigmaFiberEquiv f)
  refine ⟨G, G.e.symm.trans τ, fun i => ?_⟩
  have key : f ((G.e.symm.trans τ) i) = G.bl i := ((Fintype.equivFin {j // f j = (G.e.symm i).1}).symm (G.e.symm i).2).2
  calc res (χ ((G.e.symm.trans τ) i)) = l[((f ((G.e.symm.trans τ) i) : Fin l.length) : ℕ)] := (hf _).symm
    _ = l[((G.bl i : Fin l.length) : ℕ)] := by simp only [key]
    _ = res (G.chi i) := (hrep' (G.bl i)).symm

end Grp

end UpperTheory.TNZ
