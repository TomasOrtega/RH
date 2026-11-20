import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubrepFixedOfUnitary

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

/- English proof (translation)
Introduce `H W _ _ _ ρ B hB hinv hadm x hx`. Take `⟨K, hKx, hfin, horb⟩` from `hadm x`. Use `set V := GlobalTheory.PRep.fixed ρ K with hVdef`. Establish `memV : ∀ v, v ∈ V ↔ ∀ k ∈ K, ρ k v = v`. Introduce `v`.

Express the relevant statement in the definitionally equal form `(∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h k hk`. Simplify using `using h ⟨k, hk⟩`. Introduce `h k`.

Simplify using `using h k k.2`. Establish `hmul : ∀ a b : H, ∀ w, ρ a (ρ b w) = ρ (a * b) w`. Introduce `a b w`. Rewrite using `[map_mul, Module.End.mul_apply]`. Establish `hinvc : ∀ a : H, ∀ w, ρ a⁻¹ (ρ a w) = w`.

Introduce `a w`. Rewrite using `[hmul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `hinvc' : ∀ a : H, ∀ w, ρ a (ρ a⁻¹ w) = w`. Introduce `a w`. Rewrite using `[hmul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Establish `invB : ∀ g u v, B (ρ g u) v = B u (ρ g⁻¹ v)`. Introduce `g u v`. Rewrite using `[← hinv g⁻¹ (ρ g u) v, hinvc]`. Establish `hxV : x ∈ V` using `(memV x).2 hKx`. Establish `avg : ∀ u, ∃ u', u' ∈ V ∧ (∀ M : Submodule ℂ W, (∀ g, ∀ w ∈ M, ρ g w ∈ M) → u ∈ M → u' ∈ M) ∧ ∃ n : ℕ, 0 < n ∧ ∀ y ∈ V, B u' y = n * B u y ∧ B y u' = n * B y u`.

Introduce `u`. Establish `hO` using `horb u`. Use `⟨∑ w ∈ hO.toFinset, w, ?_, ?_, hO.toFinset.card, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[memV]`. Introduce `k hk`.

Rewrite using `[map_sum]`. Apply `Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ k⁻¹ w)` to reduce the goal to its premises. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_range] at hw ⊢`. Take `⟨k', rfl⟩` from `hw`.

Conclude with `⟨⟨k, hk⟩ * k', by rw [hmul]; rfl⟩`. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_range] at hw ⊢`. Take `⟨k', rfl⟩` from `hw`. Conclude with `⟨⟨k, hk⟩⁻¹ * k', by rw [hmul]; rfl⟩`.

Introduce `w _`. Conclude with `hinvc k w`. Introduce `w _`. Conclude with `hinvc' k w`. Introduce `w _`.

Both sides reduce to the same expression. Introduce `M hM hu`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_range] at hw`.

Take `⟨k', rfl⟩` from `hw`. Conclude with `hM _ _ hu`. Conclude with `Finset.card_pos.2 ⟨u, by simp only [Set.Finite.mem_toFinset, Set.mem_range]; exact ⟨1, by simp⟩⟩`. Introduce `y hy`. Rewrite `hy` using `[memV]`.

Establish `e1 : ∀ w ∈ hO.toFinset, B w y = B u y`. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_range] at hw`. Take `⟨k', rfl⟩` from `hw`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : ∀ w ∈ hO.toFinset, B y w = B y u`. Introduce `w hw`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_range] at hw`. Take `⟨k', rfl⟩` from `hw`. Combine the equalities or inequalities in the displayed calculation.

Prove the components needed by the constructor for the conclusion. Rewrite using `[map_sum, LinearMap.sum_apply, Finset.sum_congr rfl e1, Finset.sum_const, nsmul_eq_mul]`. Rewrite using `[map_sum, Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul]`. Establish `proj : ∀ S1 : Submodule ℂ W, FiniteDimensional ℂ S1 → ∀ v, ∃ p ∈ S1, ∀ s ∈ S1, B s (v - p) = 0`. Introduce `S1 hS1 v`.

Set `b` to `Module.finBasis ℂ S1`. Establish `ext0 : ∀ w, (∀ i, B (b i : W) w = 0) → ∀ s ∈ S1, B s w = 0`. Introduce `w hw s hs`. Establish `h` using `b.ext (f₁ := (B.flip w).comp S1.subtype) (f₂ := 0) (fun i => by simpa using hw i)`. Simplify using `using LinearMap.congr_fun h ⟨s, hs⟩`.

Set `Φ : S1 →ₗ[ℂ] (Fin (Module.finrank ℂ S1) → ℂ)` to `LinearMap.pi (fun i => (B (b i : W)).comp S1.subtype)`. Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `p hp`. Establish `h0 : ∀ i, B (b i : W) p = 0` using `fun i => by simpa [Φ] using congr_fun hp i`.

Use `ext0 p h0 p p.2` as an intermediate fact. Conclude with `Subtype.ext (by simpa using hB _ this)`. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj`. Take `⟨p, hp⟩` from `hsurj (fun i => B (b i : W) v)`. Use `⟨p, p.2, ext0 _ ?_⟩` and prove the remaining obligations.

Introduce `i`. Use `congr_fun hp i` as an intermediate fact. Simplify using `only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this`. Rewrite using `[map_sub, this, sub_self]`. Set `orth : Submodule ℂ W → Submodule ℂ W` to `fun M => ⨅ u : M, LinearMap.ker (B (u : W))`.

Establish `mem_orth : ∀ M w, w ∈ orth M ↔ ∀ u ∈ M, B u w = 0`. Introduce `M w`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]`. Establish `orth_inv : ∀ M : Submodule ℂ W, (∀ g, ∀ u ∈ M, ρ g u ∈ M) → ∀ g, ∀ w ∈ orth M, ρ g w ∈ orth M`. Introduce `M hM g w hw`.

Rewrite `hw`, the goal using `[mem_orth]`. Introduce `u hu`. Use `hw _ (hM g⁻¹ u hu)` as an intermediate fact. Rewrite `this` using `[← hinv g (ρ g⁻¹ u) w, hinvc']`. Conclude with `this`.

Establish `hBx : B x x ≠ 0` using `fun h => hx (hB x h)`. Establish `hex : ∃ d, ∃ N : Submodule ℂ W, (∀ g, ∀ u ∈ N, ρ g u ∈ N) ∧ (∃ u ∈ N, B u x ≠ 0) ∧ Module.finrank ℂ ↥(N ⊓ V) = d` using `⟨_, ⊤, fun _ _ _ => Submodule.mem_top, ⟨x, Submodule.mem_top, hBx⟩, rfl⟩`. Take `⟨N0, hN0i, ⟨u0, hu0N, hu0x⟩, hN0d⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ N : Submodule ℂ W, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → (∃ u ∈ N, B u x ≠ 0) → Nat.find hex ≤ Module.finrank ℂ ↥(N ⊓ V)` using `fun N h1 h2 => Nat.find_min' hex ⟨N, h1, h2, rfl⟩`. Use `haveI hfinV : FiniteDimensional ℂ V := hfin`.

Establish `finInf : ∀ N : Submodule ℂ W, FiniteDimensional ℂ ↥(N ⊓ V)` using `fun N => Submodule.finiteDimensional_of_le inf_le_right`. Set `U : Submodule ℂ W` to `Submodule.span ℂ {w | ∃ h : H, ∃ s ∈ N0 ⊓ V, w = ρ h s}`. Establish `hUi : ∀ g, ∀ u ∈ U, ρ g u ∈ U`. Introduce `g u hu`. Establish `: U ≤ U.comap (ρ g)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `w ⟨h, s, hs, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, hmul]`. Conclude with `Submodule.subset_span ⟨g * h, s, hs, rfl⟩`. Conclude with `this hu`.

Establish `hSU : N0 ⊓ V ≤ U` using `fun s hs => Submodule.subset_span ⟨1, s, hs, by simp⟩`. Establish `hUN : U ≤ N0`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `w ⟨h, s, hs, rfl⟩`. Conclude with `hN0i h s (Submodule.mem_inf.1 hs).1`.

Establish `hUV : U ⊓ V = N0 ⊓ V` using `le_antisymm (inf_le_inf_right _ hUN) (le_inf hSU inf_le_right)`. Take `⟨s0, hs0V, hs0M, n0, hn0, hs0B⟩` from `avg u0`. Establish `hs0S : s0 ∈ N0 ⊓ V` using `Submodule.mem_inf.2 ⟨hs0M N0 hN0i hu0N, hs0V⟩`. Establish `hs0x : B s0 x ≠ 0`. Rewrite using `[(hs0B x hxV).1]`.

Conclude with `mul_ne_zero (by exact_mod_cast hn0.ne') hu0x`. Establish `hirr : ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U`. Introduce `N hNU hNi`. Distinguish the cases in `hF : ∃ u ∈ N, B u x ≠ 0`. Use `right`.

Establish `h1` using `hmin N hNi hF`. Establish `hle : N ⊓ V ≤ N0 ⊓ V` using `by rw [← hUV]; exact inf_le_inf_right _ hNU`. Use `haveI := finInf N0`. Establish `heq : N ⊓ V = N0 ⊓ V` using `Submodule.eq_of_le_of_finrank_le hle (by rw [hN0d]; exact h1)`. Apply `le_antisymm hNU` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `w ⟨h, s, hs, rfl⟩`. Establish `: s ∈ N ⊓ V` using `by rw [heq]; exact hs`. Conclude with `hNi h s (Submodule.mem_inf.1 this).1`. Use `left push_neg at hF`.

Establish `hS1 : N ⊓ V = ⊥`. Assume the negation of the conclusion as `hne`. Take `⟨s1, hs1, hs1ne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Use `haveI := finInf N`. Take `⟨p, hp, hpq⟩` from `proj (N ⊓ V) inferInstance s0`.

Establish `hpS : p ∈ N0 ⊓ V` using `by rw [← hUV]; exact inf_le_inf_right _ hNU hp`. Establish `hpN : p ∈ N` using `(Submodule.mem_inf.1 hp).1`. Establish `hqx : B (s0 - p) x ≠ 0`. Rewrite using `[map_sub, LinearMap.sub_apply, hF p hpN, sub_zero]`. Conclude with `hs0x`.

Establish `hqV : s0 - p ∈ V` using `sub_mem hs0V (Submodule.mem_inf.1 hp).2`. Establish `hqo : s0 - p ∈ orth N`. Rewrite using `[mem_orth]`. Introduce `n hn`. Take `⟨n', hn'V, hn'M, m, hm, hnB⟩` from `avg n`.

Establish `h1` using `hpq n' (Submodule.mem_inf.2 ⟨hn'M N hNi hn, hn'V⟩)`. Rewrite `h1` using `[(hnB _ hqV).1]`. Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Conclude with `(mul_eq_zero.1 h1).resolve_left hm'`. Establish `hqS : s0 - p ∈ N0 ⊓ V` using `sub_mem hs0S hpS`.

Establish `hlt : (U ⊓ orth N) ⊓ V < N0 ⊓ V`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Rewrite using `[← hUV]`. Conclude with `inf_le_inf_right _ inf_le_left`. Introduce `heq`.

Establish `hs1S : s1 ∈ N0 ⊓ V` using `by rw [← hUV]; exact inf_le_inf_right _ hNU hs1`. Rewrite `hs1S` using `[← heq]`. Establish `ho` using `(mem_orth N s1).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hs1S).1).2 s1 (Submodule.mem_inf.1 hs1).1`. Conclude with `hs1ne (hB _ ho)`. Establish `hFN` using `hmin (U ⊓ orth N) (fun g u hu => Submodule.mem_inf.2 ⟨hUi g u (Submodule.mem_inf.1 hu).1, orth_inv N hNi g u (Submodule.mem_inf.1 hu).2⟩) ⟨s0 - p, Submodule.mem_inf.2 ⟨hSU hqS, hqo⟩, hqx⟩`.

Use `haveI := finInf N0`. Use `Submodule.finrank_lt_finrank_of_lt hlt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[eq_bot_iff]`. Introduce `v hv`.

Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `hv0`. Establish `hvv : B v v ≠ 0` using `fun h => hv0 (hB v h)`. Establish `hex2 : ∃ h : H, ∃ s ∈ N0 ⊓ V, B (ρ h s) v ≠ 0`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Establish `hle : U ≤ LinearMap.ker (B.flip v)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `w ⟨h, s, hs, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]`.

Conclude with `hall h s hs`. Use `hle (hNU hv)` as an intermediate fact. Simplify using `only [LinearMap.mem_ker, LinearMap.flip_apply] at this`. Conclude with `hvv this`. Take `⟨h, s, hs, hne⟩` from `hex2`.

Rewrite `hne` using `[invB]`. Take `⟨v', hv'V, hv'M, m, hm, hvB⟩` from `avg (ρ h⁻¹ v)`. Establish `hv'N : v' ∈ N ⊓ V` using `Submodule.mem_inf.2 ⟨hv'M N hNi (hNi _ _ hv), hv'V⟩`. Rewrite `hv'N` using `[hS1, Submodule.mem_bot]`. Establish `h2` using `(hvB s (Submodule.mem_inf.1 hs).2).2`.

Rewrite `h2` using `[hv'N, map_zero]`. Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Conclude with `hne ((mul_eq_zero.1 h2.symm).resolve_left hm')`. Use `haveI := finInf N0`. Take `⟨p, hp, hpt⟩` from `proj (N0 ⊓ V) inferInstance x`.

Establish `htU : x - p ∈ orth U`. Rewrite using `[mem_orth]`. Introduce `u hu`. Take `⟨u', hu'V, hu'M, m, hm, huB⟩` from `avg u`. Establish `hu'S : u' ∈ N0 ⊓ V` using `by rw [← hUV]; exact Submodule.mem_inf.2 ⟨hu'M U hUi hu, hu'V⟩`.

Establish `htV : x - p ∈ V` using `sub_mem hxV (Submodule.mem_inf.1 hp).2`. Establish `h1` using `hpt u' hu'S`. Rewrite `h1` using `[(huB _ htV).1]`. Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Conclude with `(mul_eq_zero.1 h1).resolve_left hm'`.

Use `⟨U, hUi, hirr, p, hSU hp, ?_, ?_⟩` and prove the remaining obligations. Introduce `hp0`. Rewrite `htU` using `[hp0, sub_zero]`. Conclude with `hs0x ((mem_orth U x).1 htU s0 (hSU hs0S))`. Introduce `κ s y c hrel`.

Establish `hpU : p ∈ U` using `hSU hp`. Establish `hr1 : ∑ i ∈ s, ρ (y i) p - c • p ∈ U` using `Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => hUi _ _ hpU) (Submodule.smul_mem _ _ hpU)`. Establish `hr2 : ∑ i ∈ s, ρ (y i) p - c • p ∈ orth U`. Establish `e : ∑ i ∈ s, ρ (y i) p - c • p = -(∑ i ∈ s, ρ (y i) (x - p) - c • (x - p))`. Simplify using `only [map_sub, Finset.sum_sub_distrib, smul_sub, hrel]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.neg_mem _ (Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => orth_inv U hUi _ _ htU) (Submodule.smul_mem _ _ htU))`. Use `(mem_orth U _).1 hr2 _ hr1` as an intermediate fact. Conclude with `sub_eq_zero.1 (hB _ this)`.
-/
theorem UpperTheory.exists_irreducible_subrep_hecke_eigen_of_invariant_form :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ),
        (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) →
        (∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧ ∀ w, (Set.range fun k : K => ρ k w).Finite) →
        ∀ x : W, x ≠ 0 → ∃ U : Submodule ℂ W, (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) ∧
          ∃ f ∈ U, f ≠ 0 ∧ ∀ (κ : Type) (s : Finset κ) (y : κ → H) (c : ℂ), ∑ i ∈ s, ρ (y i) x = c • x → ∑ i ∈ s, ρ (y i) f = c • f := by
  intro H W _ _ _ ρ B hB hinv hadm x hx
  classical
  obtain ⟨K, hKx, hfin, horb⟩ := hadm x
  set V := GlobalTheory.PRep.fixed ρ K with hVdef
  have memV : ∀ v, v ∈ V ↔ ∀ k ∈ K, ρ k v = v := by
    intro v
    change (∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
    constructor
    · intro h k hk
      simpa using h ⟨k, hk⟩
    · intro h k
      simpa using h k k.2
  have hmul : ∀ a b : H, ∀ w, ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  have hinvc : ∀ a : H, ∀ w, ρ a⁻¹ (ρ a w) = w := by
    intro a w
    rw [hmul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinvc' : ∀ a : H, ∀ w, ρ a (ρ a⁻¹ w) = w := by
    intro a w
    rw [hmul, mul_inv_cancel, map_one, Module.End.one_apply]
  have invB : ∀ g u v, B (ρ g u) v = B u (ρ g⁻¹ v) := by
    intro g u v
    rw [← hinv g⁻¹ (ρ g u) v, hinvc]
  have hxV : x ∈ V := (memV x).2 hKx
  have avg : ∀ u, ∃ u', u' ∈ V ∧ (∀ M : Submodule ℂ W, (∀ g, ∀ w ∈ M, ρ g w ∈ M) → u ∈ M → u' ∈ M) ∧
      ∃ n : ℕ, 0 < n ∧ ∀ y ∈ V, B u' y = n * B u y ∧ B y u' = n * B y u := by
    intro u
    have hO := horb u
    refine ⟨∑ w ∈ hO.toFinset, w, ?_, ?_, hO.toFinset.card, ?_, ?_⟩
    · rw [memV]
      intro k hk
      rw [map_sum]
      apply Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ k⁻¹ w)
      · intro w hw
        simp only [Set.Finite.mem_toFinset, Set.mem_range] at hw ⊢
        obtain ⟨k', rfl⟩ := hw
        exact ⟨⟨k, hk⟩ * k', by rw [hmul]; rfl⟩
      · intro w hw
        simp only [Set.Finite.mem_toFinset, Set.mem_range] at hw ⊢
        obtain ⟨k', rfl⟩ := hw
        exact ⟨⟨k, hk⟩⁻¹ * k', by rw [hmul]; rfl⟩
      · intro w _
        exact hinvc k w
      · intro w _
        exact hinvc' k w
      · intro w _
        rfl
    · intro M hM hu
      apply Submodule.sum_mem
      intro w hw
      simp only [Set.Finite.mem_toFinset, Set.mem_range] at hw
      obtain ⟨k', rfl⟩ := hw
      exact hM _ _ hu
    · exact Finset.card_pos.2 ⟨u, by simp only [Set.Finite.mem_toFinset, Set.mem_range]; exact ⟨1, by simp⟩⟩
    · intro y hy
      rw [memV] at hy
      have e1 : ∀ w ∈ hO.toFinset, B w y = B u y := by
        intro w hw
        simp only [Set.Finite.mem_toFinset, Set.mem_range] at hw
        obtain ⟨k', rfl⟩ := hw
        calc B (ρ k' u) y = B (ρ k' u) (ρ k' y) := by rw [hy k' k'.2]
          _ = B u y := hinv _ _ _
      have e2 : ∀ w ∈ hO.toFinset, B y w = B y u := by
        intro w hw
        simp only [Set.Finite.mem_toFinset, Set.mem_range] at hw
        obtain ⟨k', rfl⟩ := hw
        calc B y (ρ k' u) = B (ρ k' y) (ρ k' u) := by rw [hy k' k'.2]
          _ = B y u := hinv _ _ _
      constructor
      · rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl e1, Finset.sum_const, nsmul_eq_mul]
      · rw [map_sum, Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul]
  have proj : ∀ S1 : Submodule ℂ W, FiniteDimensional ℂ S1 → ∀ v, ∃ p ∈ S1, ∀ s ∈ S1, B s (v - p) = 0 := by
    intro S1 hS1 v
    let b := Module.finBasis ℂ S1
    have ext0 : ∀ w, (∀ i, B (b i : W) w = 0) → ∀ s ∈ S1, B s w = 0 := by
      intro w hw s hs
      have h := b.ext (f₁ := (B.flip w).comp S1.subtype) (f₂ := 0) (fun i => by simpa using hw i)
      simpa using LinearMap.congr_fun h ⟨s, hs⟩
    let Φ : S1 →ₗ[ℂ] (Fin (Module.finrank ℂ S1) → ℂ) := LinearMap.pi (fun i => (B (b i : W)).comp S1.subtype)
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro p hp
      have h0 : ∀ i, B (b i : W) p = 0 := fun i => by simpa [Φ] using congr_fun hp i
      have := ext0 p h0 p p.2
      exact Subtype.ext (by simpa using hB _ this)
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
    obtain ⟨p, hp⟩ := hsurj (fun i => B (b i : W) v)
    refine ⟨p, p.2, ext0 _ ?_⟩
    intro i
    have := congr_fun hp i
    simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [map_sub, this, sub_self]
  let orth : Submodule ℂ W → Submodule ℂ W := fun M => ⨅ u : M, LinearMap.ker (B (u : W))
  have mem_orth : ∀ M w, w ∈ orth M ↔ ∀ u ∈ M, B u w = 0 := by
    intro M w
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  have orth_inv : ∀ M : Submodule ℂ W, (∀ g, ∀ u ∈ M, ρ g u ∈ M) → ∀ g, ∀ w ∈ orth M, ρ g w ∈ orth M := by
    intro M hM g w hw
    rw [mem_orth] at hw ⊢
    intro u hu
    have := hw _ (hM g⁻¹ u hu)
    rw [← hinv g (ρ g⁻¹ u) w, hinvc'] at this
    exact this
  have hBx : B x x ≠ 0 := fun h => hx (hB x h)
  have hex : ∃ d, ∃ N : Submodule ℂ W, (∀ g, ∀ u ∈ N, ρ g u ∈ N) ∧ (∃ u ∈ N, B u x ≠ 0) ∧
      Module.finrank ℂ ↥(N ⊓ V) = d :=
    ⟨_, ⊤, fun _ _ _ => Submodule.mem_top, ⟨x, Submodule.mem_top, hBx⟩, rfl⟩
  obtain ⟨N0, hN0i, ⟨u0, hu0N, hu0x⟩, hN0d⟩ := Nat.find_spec hex
  have hmin : ∀ N : Submodule ℂ W, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → (∃ u ∈ N, B u x ≠ 0) →
      Nat.find hex ≤ Module.finrank ℂ ↥(N ⊓ V) :=
    fun N h1 h2 => Nat.find_min' hex ⟨N, h1, h2, rfl⟩
  haveI hfinV : FiniteDimensional ℂ V := hfin
  have finInf : ∀ N : Submodule ℂ W, FiniteDimensional ℂ ↥(N ⊓ V) :=
    fun N => Submodule.finiteDimensional_of_le inf_le_right
  let U : Submodule ℂ W := Submodule.span ℂ {w | ∃ h : H, ∃ s ∈ N0 ⊓ V, w = ρ h s}
  have hUi : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
    intro g u hu
    have : U ≤ U.comap (ρ g) := by
      rw [Submodule.span_le]
      rintro w ⟨h, s, hs, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hmul]
      exact Submodule.subset_span ⟨g * h, s, hs, rfl⟩
    exact this hu
  have hSU : N0 ⊓ V ≤ U := fun s hs => Submodule.subset_span ⟨1, s, hs, by simp⟩
  have hUN : U ≤ N0 := by
    rw [Submodule.span_le]
    rintro w ⟨h, s, hs, rfl⟩
    exact hN0i h s (Submodule.mem_inf.1 hs).1
  have hUV : U ⊓ V = N0 ⊓ V := le_antisymm (inf_le_inf_right _ hUN) (le_inf hSU inf_le_right)
  obtain ⟨s0, hs0V, hs0M, n0, hn0, hs0B⟩ := avg u0
  have hs0S : s0 ∈ N0 ⊓ V := Submodule.mem_inf.2 ⟨hs0M N0 hN0i hu0N, hs0V⟩
  have hs0x : B s0 x ≠ 0 := by
    rw [(hs0B x hxV).1]
    exact mul_ne_zero (by exact_mod_cast hn0.ne') hu0x
  have hirr : ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U := by
    intro N hNU hNi
    by_cases hF : ∃ u ∈ N, B u x ≠ 0
    · right
      have h1 := hmin N hNi hF
      have hle : N ⊓ V ≤ N0 ⊓ V := by rw [← hUV]; exact inf_le_inf_right _ hNU
      haveI := finInf N0
      have heq : N ⊓ V = N0 ⊓ V := Submodule.eq_of_le_of_finrank_le hle (by rw [hN0d]; exact h1)
      apply le_antisymm hNU
      rw [Submodule.span_le]
      rintro w ⟨h, s, hs, rfl⟩
      have : s ∈ N ⊓ V := by rw [heq]; exact hs
      exact hNi h s (Submodule.mem_inf.1 this).1
    · left
      push_neg at hF
      have hS1 : N ⊓ V = ⊥ := by
        by_contra hne
        obtain ⟨s1, hs1, hs1ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        haveI := finInf N
        obtain ⟨p, hp, hpq⟩ := proj (N ⊓ V) inferInstance s0
        have hpS : p ∈ N0 ⊓ V := by rw [← hUV]; exact inf_le_inf_right _ hNU hp
        have hpN : p ∈ N := (Submodule.mem_inf.1 hp).1
        have hqx : B (s0 - p) x ≠ 0 := by
          rw [map_sub, LinearMap.sub_apply, hF p hpN, sub_zero]
          exact hs0x
        have hqV : s0 - p ∈ V := sub_mem hs0V (Submodule.mem_inf.1 hp).2
        have hqo : s0 - p ∈ orth N := by
          rw [mem_orth]
          intro n hn
          obtain ⟨n', hn'V, hn'M, m, hm, hnB⟩ := avg n
          have h1 := hpq n' (Submodule.mem_inf.2 ⟨hn'M N hNi hn, hn'V⟩)
          rw [(hnB _ hqV).1] at h1
          have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
          exact (mul_eq_zero.1 h1).resolve_left hm'
        have hqS : s0 - p ∈ N0 ⊓ V := sub_mem hs0S hpS
        have hlt : (U ⊓ orth N) ⊓ V < N0 ⊓ V := by
          refine lt_of_le_of_ne ?_ ?_
          · rw [← hUV]
            exact inf_le_inf_right _ inf_le_left
          · intro heq
            have hs1S : s1 ∈ N0 ⊓ V := by rw [← hUV]; exact inf_le_inf_right _ hNU hs1
            rw [← heq] at hs1S
            have ho := (mem_orth N s1).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hs1S).1).2 s1
              (Submodule.mem_inf.1 hs1).1
            exact hs1ne (hB _ ho)
        have hFN := hmin (U ⊓ orth N)
          (fun g u hu => Submodule.mem_inf.2 ⟨hUi g u (Submodule.mem_inf.1 hu).1,
            orth_inv N hNi g u (Submodule.mem_inf.1 hu).2⟩)
          ⟨s0 - p, Submodule.mem_inf.2 ⟨hSU hqS, hqo⟩, hqx⟩
        haveI := finInf N0
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      by_contra hv0
      have hvv : B v v ≠ 0 := fun h => hv0 (hB v h)
      have hex2 : ∃ h : H, ∃ s ∈ N0 ⊓ V, B (ρ h s) v ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hle : U ≤ LinearMap.ker (B.flip v) := by
          rw [Submodule.span_le]
          rintro w ⟨h, s, hs, rfl⟩
          simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
          exact hall h s hs
        have := hle (hNU hv)
        simp only [LinearMap.mem_ker, LinearMap.flip_apply] at this
        exact hvv this
      obtain ⟨h, s, hs, hne⟩ := hex2
      rw [invB] at hne
      obtain ⟨v', hv'V, hv'M, m, hm, hvB⟩ := avg (ρ h⁻¹ v)
      have hv'N : v' ∈ N ⊓ V := Submodule.mem_inf.2 ⟨hv'M N hNi (hNi _ _ hv), hv'V⟩
      rw [hS1, Submodule.mem_bot] at hv'N
      have h2 := (hvB s (Submodule.mem_inf.1 hs).2).2
      rw [hv'N, map_zero] at h2
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      exact hne ((mul_eq_zero.1 h2.symm).resolve_left hm')
  haveI := finInf N0
  obtain ⟨p, hp, hpt⟩ := proj (N0 ⊓ V) inferInstance x
  have htU : x - p ∈ orth U := by
    rw [mem_orth]
    intro u hu
    obtain ⟨u', hu'V, hu'M, m, hm, huB⟩ := avg u
    have hu'S : u' ∈ N0 ⊓ V := by rw [← hUV]; exact Submodule.mem_inf.2 ⟨hu'M U hUi hu, hu'V⟩
    have htV : x - p ∈ V := sub_mem hxV (Submodule.mem_inf.1 hp).2
    have h1 := hpt u' hu'S
    rw [(huB _ htV).1] at h1
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    exact (mul_eq_zero.1 h1).resolve_left hm'
  refine ⟨U, hUi, hirr, p, hSU hp, ?_, ?_⟩
  · intro hp0
    rw [hp0, sub_zero] at htU
    exact hs0x ((mem_orth U x).1 htU s0 (hSU hs0S))
  · intro κ s y c hrel
    have hpU : p ∈ U := hSU hp
    have hr1 : ∑ i ∈ s, ρ (y i) p - c • p ∈ U :=
      Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => hUi _ _ hpU) (Submodule.smul_mem _ _ hpU)
    have hr2 : ∑ i ∈ s, ρ (y i) p - c • p ∈ orth U := by
      have e : ∑ i ∈ s, ρ (y i) p - c • p = -(∑ i ∈ s, ρ (y i) (x - p) - c • (x - p)) := by
        simp only [map_sub, Finset.sum_sub_distrib, smul_sub, hrel]
        abel
      rw [e]
      exact Submodule.neg_mem _ (Submodule.sub_mem _
        (Submodule.sum_mem _ fun i _ => orth_inv U hUi _ _ htU) (Submodule.smul_mem _ _ htU))
    have := (mem_orth U _).1 hr2 _ hr1
    exact sub_eq_zero.1 (hB _ this)
