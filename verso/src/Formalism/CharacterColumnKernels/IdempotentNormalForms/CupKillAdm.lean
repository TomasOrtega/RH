import Formalism.CharacterColumnKernels.StatGlobalModule

namespace Formalism.NG
open Module

/- English proof (translation)
Distinguish the cases in `hker : LinearMap.ker (colD (K := K) (V := V) r χ D) = ⊥`. Establish `hfin : Module.finrank K (LinearMap.ker (colD (K` using `K) (V := V) r χ D)) = 0 := by`. Rewrite using `[hker]`. Simplify using the standard rewrite rules. Rewrite `hQ` using `[hfin]`.

Set `ψ : ((Fin j → K) × K) →ₗ[K] (D → V)` to `{ toFun := fun x => ∑ a, x.1 a • (fun g : D => Kc a g • s1) + x.2 • (fun g : D => k0 g • η) map_add' := fun x y => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add, Finset.smul_sum] }`.

Establish `hψ : ∀ x, ψ x ∈ L` using `fun x => L.add_mem (L.sum_mem fun a _ => L.smul_mem _ (hK a)) (L.smul_mem _ hk)`. Set `π` to `((LinearMap.range (colD (K := K) (V := V) r χ D)).comap L.subtype).mkQ ∘ₗ LinearMap.codRestrict L ψ hψ`. Establish `hnot : ¬ Function.Injective π`. Introduce `hinj`. Establish `h1 : Module.finrank K (LinearMap.range π) = j + 1`.

Rewrite using `[LinearMap.finrank_range_of_inj hinj]`. Simplify using the standard rewrite rules. Establish `h2 : Module.rank K (LinearMap.range π) ≤ _` using `Submodule.rank_le (LinearMap.range π)`. Rewrite `h2` using `[← Module.finrank_eq_rank, h1]`. Establish `h3 : j + 1 ≤ j + 0` using `by exact_mod_cast h2.trans hQ`.

Use linear arithmetic over natural numbers and integers. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 (fun h => hnot (LinearMap.ker_eq_bot.1 h))`. Establish `hx' : LinearMap.codRestrict L ψ hψ x ∈ (LinearMap.range (colD (K` using `K) (V := V) r χ D)).comap L.subtype := by`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Conclude with `LinearMap.mem_ker.1 hx`.

Take `⟨v, hv⟩ : ψ x ∈ LinearMap.range (colD (K` from `K) (V := V) r χ D) := hx'`. Use `⟨(v, x.1, x.2), fun h => hx0 (Prod.ext (congrArg (fun p => p.2.1) h) (congrArg (fun p => p.2.2) h)), fun g hg => ?_⟩` and prove the remaining obligations. Establish `e1 : ψ x ⟨g, hg⟩ = ∑ a, x.1 a • (Kc a g • s1) + x.2 • (k0 g • η)`. Simplify using `only [ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]`. Rewrite using `[← e1, ← hv]`.

Both sides reduce to the same expression. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 hker`. Use `⟨(v, 0, 0), fun h => hv0 (congrArg Prod.fst h), fun g hg => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (LinearMap.mem_ker.1 hv) ⟨g, hg⟩`. Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]`.

Conclude with `h.symm`.
-/
private theorem place_kernel {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V] [FiniteDimensional K V]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) (j : ℕ) (Kc : Fin j → G → A) (k0 : G → A)
    (s1 η : V) (L : Submodule K (D → V))
    (hB : LinearMap.range (colD (K := K) (V := V) r χ D) ≤ L)
    (hK : ∀ a, (fun g : D => Kc a g • s1) ∈ L) (hk : (fun g : D => k0 g • η) ∈ L)
    (hQ : Module.rank K (L ⧸ (LinearMap.range (colD (K := K) (V := V) r χ D)).comap L.subtype) ≤
        (j + Module.finrank K (LinearMap.ker (colD (K := K) (V := V) r χ D)) : ℕ)) :
    ∃ p : V × (Fin j → K) × K, p ≠ 0 ∧ ∀ g ∈ D,
      ∑ a, p.2.1 a • (Kc a g • s1) + p.2.2 • (k0 g • η) =
        ((((χ g)⁻¹ : T'ˣ) : T') • r g) • p.1 - p.1 := by
  classical
  by_cases hker : LinearMap.ker (colD (K := K) (V := V) r χ D) = ⊥
  · have hfin : Module.finrank K (LinearMap.ker (colD (K := K) (V := V) r χ D)) = 0 := by
      rw [hker]; simp
    rw [hfin] at hQ
    let ψ : ((Fin j → K) × K) →ₗ[K] (D → V) :=
      { toFun := fun x => ∑ a, x.1 a • (fun g : D => Kc a g • s1) + x.2 • (fun g : D => k0 g • η)
        map_add' := fun x y => by
          simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          abel
        map_smul' := fun c x => by
          simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
            RingHom.id_apply, smul_add, Finset.smul_sum] }
    have hψ : ∀ x, ψ x ∈ L := fun x =>
      L.add_mem (L.sum_mem fun a _ => L.smul_mem _ (hK a)) (L.smul_mem _ hk)
    let π := ((LinearMap.range (colD (K := K) (V := V) r χ D)).comap L.subtype).mkQ ∘ₗ
      LinearMap.codRestrict L ψ hψ
    have hnot : ¬ Function.Injective π := by
      intro hinj
      have h1 : Module.finrank K (LinearMap.range π) = j + 1 := by
        rw [LinearMap.finrank_range_of_inj hinj]; simp
      have h2 : Module.rank K (LinearMap.range π) ≤ _ := Submodule.rank_le (LinearMap.range π)
      rw [← Module.finrank_eq_rank, h1] at h2
      have h3 : j + 1 ≤ j + 0 := by exact_mod_cast h2.trans hQ
      omega
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (fun h => hnot (LinearMap.ker_eq_bot.1 h))
    have hx' : LinearMap.codRestrict L ψ hψ x ∈
        (LinearMap.range (colD (K := K) (V := V) r χ D)).comap L.subtype := by
      rw [← Submodule.Quotient.mk_eq_zero]; exact LinearMap.mem_ker.1 hx
    obtain ⟨v, hv⟩ : ψ x ∈ LinearMap.range (colD (K := K) (V := V) r χ D) := hx'
    refine ⟨(v, x.1, x.2), fun h => hx0 (Prod.ext (congrArg (fun p => p.2.1) h)
      (congrArg (fun p => p.2.2) h)), fun g hg => ?_⟩
    have e1 : ψ x ⟨g, hg⟩ = ∑ a, x.1 a • (Kc a g • s1) + x.2 • (k0 g • η) := by
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    rw [← e1, ← hv]
    rfl
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hker
    refine ⟨(v, 0, 0), fun h => hv0 (congrArg Prod.fst h), fun g hg => ?_⟩
    have h := congrFun (LinearMap.mem_ker.1 hv) ⟨g, hg⟩
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    exact h.symm

section Hom
variable {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [Module T' V] [IsScalarTower T' A V]
    {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [Fintype ι] [DecidableEq ι] {j : ι → ℕ}

private def colFreeMap (φY : Ymod r χ E →ₗ[A] V) (n : ι → V) (s : (l : ι) → Fin (j l) → V) (s0 : ι → V) :
    ColFreeJ A r χ E ι j →ₗ[A] V where
  toFun x := φY x.1 + ∑ l, ((x.2 l).1 • n l + ∑ a, (x.2 l).2.1 a • s l a + (x.2 l).2.2 • s0 l)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add, Finset.smul_sum]

/- English proof (translation)
Rewrite using `[colGenJ]`. Simplify using `only [colFreeMap, LinearMap.coe_mk, AddHom.coe_mk]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ l) h`.
-/
private theorem colFreeMap_colGen (φY : Ymod r χ E →ₗ[A] V) (n : ι → V) (s : (l : ι) → Fin (j l) → V) (s0 : ι → V)
    (y : Ymod r χ E) (l : ι) (c : A) (sv : Fin (j l) → A) (c₀ : A) :
    colFreeMap φY n s s0 (colGenJ y l c sv c₀) =
      φY y + (c • n l + ∑ a, sv a • s l a + c₀ • s0 l) := by
  rw [colGenJ]
  simp only [colFreeMap, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ l) h

/- English proof (translation)
Use `⟨(colRelJ r χ E e₁ δ D j Kc k0).liftQ (colFreeMap φY n s s0) ?_, fun x => rfl⟩` and prove the remaining obligations. Unfold `colRelJ`. Rewrite using `[Submodule.span_le]`. Use `Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, rfl⟩`.

Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]`. Simplify using `[h1]`. Introduce and unpack `_ ⟨l, a, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]`. Simplify using `[Pi.single_apply, ite_smul, sub_smul, h2]`.

Introduce and unpack `_ ⟨l, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]`. Simplify using `[algebraMap_smul, sub_smul, hδ, h3]`. Introduce and unpack `_ ⟨l, g, hg, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]`.

Establish `key` using `h4 l g hg`. Rewrite `key` using `[smul_add, Finset.smul_sum, ← sub_eq_zero]`. Simplify using `only [neg_smul, mul_smul, algebraMap_smul, hδ, sub_smul, one_smul, Finset.sum_neg_distrib]`. Rewrite using `[← key]`. Normalize the expressions using the abelian group laws.
-/
private theorem colHom_exists (e₁ : A) (δ : T') (D : ι → Subgroup G) (Kc : ∀ l, Fin (j l) → G → A)
    (k0 : ι → G → A) (δx : K) (hδ : ∀ v : V, δ • v = δx • v)
    (φY : Ymod r χ E →ₗ[A] V) (n : ι → V) (s : (l : ι) → Fin (j l) → V) (s0 : ι → V)
    (h1 : ∀ l, E • n l = 0) (h2 : ∀ l a, e₁ • s l a = s l a)
    (h3 : ∀ l, E • s0 l = δx • s0 l)
    (h4 : ∀ l, ∀ g ∈ D l, φY ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ +
      ((((χ g)⁻¹ : T'ˣ) : T') • r g) • n l - n l =
        δx • (∑ a, Kc l a g • s l a + k0 l g • s0 l)) :
    ∃ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] V, ∀ x : ColFreeJ A r χ E ι j,
      φ (Submodule.Quotient.mk x) = colFreeMap φY n s s0 x := by
  refine ⟨(colRelJ r χ E e₁ δ D j Kc k0).liftQ (colFreeMap φY n s s0) ?_, fun x => rfl⟩
  unfold colRelJ
  rw [Submodule.span_le]
  refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
  · rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    simp [h1]
  · rintro _ ⟨l, a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    simp [Pi.single_apply, ite_smul, sub_smul, h2]
  · rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    simp [algebraMap_smul, sub_smul, hδ, h3]
  · rintro _ ⟨l, g, hg, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, colFreeMap_colGen]
    have key := h4 l g hg
    rw [smul_add, Finset.smul_sum, ← sub_eq_zero] at key
    simp only [neg_smul, mul_smul, algebraMap_smul, hδ, sub_smul, one_smul, Finset.sum_neg_distrib]
    rw [← key]
    abel

end Hom

/- English proof (translation)
Introduce `A T' K V G _ _ _ _ _ _ _ _ _ _ _ _ r χ E e₁ δ ι _ _ D j Kc k0 hE he₁ δx hδx hδ hrE hre₁ hfix hL`. Take `⟨xη, hxη⟩` from `(Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (hrE ▸ Nat.one_pos)`. Take `⟨x1, hx1⟩` from `(Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (hre₁ ▸ Nat.one_pos)`. Establish `hspan` using `(finrank_eq_one_iff_of_nonzero' xη hxη).mp hrE`. Use `set η : V := (xη : V) with hηdef`.

Use `set s1 : V := (x1 : V) with hs1def`. Establish `hηmem : η ∈ LinearMap.range (DistribSMul.toLinearMap K V E)` using `xη.2`. Establish `hs1mem : s1 ∈ LinearMap.range (DistribSMul.toLinearMap K V e₁)` using `x1.2`. Establish `hη0 : η ≠ 0` using `fun h => hxη (Subtype.ext h)`. Establish `hs10 : s1 ≠ 0` using `fun h => hx1 (Subtype.ext h)`.

Take `⟨w0, hw0⟩` from `hηmem`. Take `⟨w1, hw1⟩` from `hs1mem`. Rewrite `hw0`, `hw1` using `[DistribSMul.toLinearMap_apply]`. Establish `hδA : ∀ w : V, algebraMap T' A δ • w = δx • w`. Introduce `w`.

Rewrite using `[algebraMap_smul, hδ]`. Establish `hEη : E • η = δx • η`. Rewrite using `[← hw0, smul_smul, hE, mul_smul, hδA]`. Establish `he₁s1 : e₁ • s1 = s1`. Rewrite using `[← hw1, smul_smul, he₁]`.

Establish `hplace : ∀ l, ∃ p : V × (Fin (j l) → K) × K, (∀ g ∈ D l, ∑ a, p.2.1 a • (Kc l a g • s1) + p.2.2 • (k0 l g • η) = ((((χ g)⁻¹ : T'ˣ) : T') • r g) • p.1 - p.1) ∧ ((E • p.1 = 0 ∧ p ≠ 0) ∨ E • p.1 = η)`. Introduce `l`. Take `⟨L, hB, hK, hk, hQ⟩` from `hL l`. Take `⟨p, hp0, hp⟩` from `place_kernel r χ (D l) (j l) (Kc l) (k0 l) s1 η L hB (fun a => hK a s1 x1.2) (hk η xη.2) hQ`. Distinguish the cases in `hE0 : E • p.1 = 0`.

Conclude with `⟨p, hp, Or.inl ⟨hE0, hp0⟩⟩`. Take `⟨t, ht⟩` from `hspan ⟨E • p.1, p.1, rfl⟩`. Establish `ht' : t • η = E • p.1` using `congrArg Subtype.val ht`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`.

Rewrite `ht'` using `[zero_smul]`. Conclude with `hE0 ht'.symm`. Use `⟨t⁻¹ • p, ?_, Or.inr ?_⟩` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← smul_add, hp g hg, smul_sub, smul_comm _ t⁻¹ p.1]`.

Simplify using `only [Prod.smul_fst]`. Rewrite using `[smul_comm, ← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Use `choose P hPrel hPn using hplace`. Distinguish the cases in `hA : ∃ l0, E • (P l0).1 = 0 ∧ P l0 ≠ 0`. Take `⟨l0, hEv, hP0⟩` from `hA`.

Take `⟨φ, hφ⟩` from `colHom_exists (V := V) e₁ δ D Kc k0 δx hδ 0 (fun l => if l = l0 then δx • (P l).1 else 0) (fun l a => if l = l0 then (P l).2.1 a • s1 else 0) (fun l => if l = l0 then (P l).2.2 • η else 0) (by`. Introduce `l`. Use `split_ifs with hl`. Substitute `hl` using the available equality. Rewrite using `[smul_comm E δx, hEv, smul_zero]`.

Conclude with `smul_zero E)`. Use the proof step `(by`. Introduce `l a`. Use `split_ifs with hl`. Substitute `hl` using the available equality.

Rewrite using `[smul_comm e₁ ((P l).2.1 a) s1, he₁s1]`. Conclude with `smul_zero e₁)`. Use the proof step `(by`. Introduce `l`. Use `split_ifs with hl`.

Substitute `hl` using the available equality. Rewrite using `[smul_comm E (P l).2.2 η, hEη, smul_comm (P l).2.2 δx η]`. Rewrite using `[smul_zero, smul_zero])`. Use the proof step `(by`. Introduce `l g hg`.

Use `split_ifs with hl`. Substitute `hl` using the available equality. Establish `hsum : ∀ a, Kc l a g • ((P l).2.1 a • s1) = (P l).2.1 a • (Kc l a g • s1)` using `fun a => smul_comm _ _ _`. Rewrite using `[LinearMap.zero_apply, zero_add]`. Simplify using `only [hsum]`.

Rewrite using `[smul_comm (k0 l g) (P l).2.2 η, hPrel l g hg, smul_sub, smul_comm ((((χ g)⁻¹ : T'ˣ) : T') • r g) δx (P l).1]`. Use the proof step `simp)`. Use `⟨φ, fun h0 => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x, colFreeMap (0 : Ymod r χ E →ₗ[A] V) (fun l => if l = l0 then δx • (P l).1 else 0) (fun l a => if l = l0 then (P l).2.1 a • s1 else 0) (fun l => if l = l0 then (P l).2.2 • η else 0) x = 0`. Introduce `x`.

Rewrite using `[← hφ, h0, LinearMap.zero_apply]`. Establish `hne : (P l0).1 ≠ 0 ∨ (∃ a, (P l0).2.1 a ≠ 0) ∨ (P l0).2.2 ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hP0 (Prod.ext hc.1 (Prod.ext (funext hc.2.1) hc.2.2))`.

Break down `hne with hv | ⟨a, ha⟩ | hc0` into its components or cases. Use `key (colGenJ 0 l0 1 0 0)` as an intermediate fact. Simplify using `only [colFreeMap_colGen] at this`. Simplify using `[hv, hδx] at this`. Use `key (colGenJ 0 l0 0 (Pi.single a 1) 0)` as an intermediate fact.

Simplify using `only [colFreeMap_colGen] at this`. Rewrite `this` using `[Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (fun h => absurd (Finset.mem_univ a) h)]`. Simplify using `[ha, hs10] at this`. Use `key (colGenJ 0 l0 0 0 1)` as an intermediate fact. Simplify using `only [colFreeMap_colGen] at this`.

Simplify using `[hc0, hη0] at this`. Use `push Not at hA`. Establish `hEP : ∀ l, E • (P l).1 = η`. Introduce `l`. Break down `hPn l with ⟨h1, h2⟩ | h` into its components or cases.

Conclude with `absurd (hA l h1) h2`. Conclude with `h`. Set `φY : Ymod r χ E →ₗ[A] V` to `(LinearMap.toSpanSingleton A V w0).comp (Ymod r χ E).subtype`. Establish `hφY : ∀ g, φY ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ = ((((χ g)⁻¹ : T'ˣ) : T') • r g) • η - η`. Introduce `g`.

Simplify using `only [φY, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply, ycoc, mul_smul, hw0, sub_smul, one_smul]`. Take `⟨φ, hφ⟩` from `colHom_exists (V := V) e₁ δ D Kc k0 δx hδ φY (fun l => δx • (P l).1 - η) (fun l a => (P l).2.1 a • s1) (fun l => (P l).2.2 • η) (by intro l; rw [smul_sub, smul_comm E δx, hEP, hEη, sub_self]) (by intro l a; rw [smul_comm e₁ ((P l).2.1 a) s1, he₁s1]) (by intro l; rw [smul_comm E ( …`. Introduce `l g hg`. Establish `hsum : ∀ a, Kc l a g • ((P l).2.1 a • s1) = (P l).2.1 a • (Kc l a g • s1)` using `fun a => smul_comm _ _ _`. Rewrite using `[hφY]`.

Simplify using `only [hsum]`. Rewrite using `[smul_comm (k0 l g) (P l).2.2 η, hPrel l g hg, smul_sub, smul_sub, smul_comm ((((χ g)⁻¹ : T'ˣ) : T') • r g) δx (P l).1]`. Use the proof step `abel)`. Take `⟨g, hg⟩` from `hfix η ⟨w0, by rw [DistribSMul.toLinearMap_apply, hw0]⟩ hη0`. Use `⟨φ, fun h0 => ?_⟩` and prove the remaining obligations.

Use `hφ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩, 0)` as an intermediate fact. Rewrite `this` using `[h0, LinearMap.zero_apply]`. Simplify using `only [colFreeMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero, zero_smul, Finset.sum_const_zero, add_zero, hφY] at this`. Conclude with `hg (sub_eq_zero.mp this.symm)`.
-/
theorem columnJ : StatColumnJ := by
  intro A T' K V G _ _ _ _ _ _ _ _ _ _ _ _ r χ E e₁ δ ι _ _ D j Kc k0 hE he₁ δx hδx hδ hrE hre₁
    hfix hL

  obtain ⟨xη, hxη⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (hrE ▸ Nat.one_pos)
  obtain ⟨x1, hx1⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (hre₁ ▸ Nat.one_pos)
  have hspan := (finrank_eq_one_iff_of_nonzero' xη hxη).mp hrE
  set η : V := (xη : V) with hηdef
  set s1 : V := (x1 : V) with hs1def
  have hηmem : η ∈ LinearMap.range (DistribSMul.toLinearMap K V E) := xη.2
  have hs1mem : s1 ∈ LinearMap.range (DistribSMul.toLinearMap K V e₁) := x1.2
  have hη0 : η ≠ 0 := fun h => hxη (Subtype.ext h)
  have hs10 : s1 ≠ 0 := fun h => hx1 (Subtype.ext h)
  obtain ⟨w0, hw0⟩ := hηmem
  obtain ⟨w1, hw1⟩ := hs1mem
  rw [DistribSMul.toLinearMap_apply] at hw0 hw1
  have hδA : ∀ w : V, algebraMap T' A δ • w = δx • w := by
    intro w; rw [algebraMap_smul, hδ]
  have hEη : E • η = δx • η := by
    rw [← hw0, smul_smul, hE, mul_smul, hδA]
  have he₁s1 : e₁ • s1 = s1 := by
    rw [← hw1, smul_smul, he₁]

  have hplace : ∀ l, ∃ p : V × (Fin (j l) → K) × K,
      (∀ g ∈ D l, ∑ a, p.2.1 a • (Kc l a g • s1) + p.2.2 • (k0 l g • η) =
        ((((χ g)⁻¹ : T'ˣ) : T') • r g) • p.1 - p.1) ∧
      ((E • p.1 = 0 ∧ p ≠ 0) ∨ E • p.1 = η) := by
    intro l
    obtain ⟨L, hB, hK, hk, hQ⟩ := hL l
    obtain ⟨p, hp0, hp⟩ := place_kernel r χ (D l) (j l) (Kc l) (k0 l) s1 η L hB
      (fun a => hK a s1 x1.2)
      (hk η xη.2) hQ
    by_cases hE0 : E • p.1 = 0
    · exact ⟨p, hp, Or.inl ⟨hE0, hp0⟩⟩
    · obtain ⟨t, ht⟩ := hspan ⟨E • p.1, p.1, rfl⟩
      have ht' : t • η = E • p.1 := congrArg Subtype.val ht
      have ht0 : t ≠ 0 := by
        rintro rfl; rw [zero_smul] at ht'; exact hE0 ht'.symm
      refine ⟨t⁻¹ • p, ?_, Or.inr ?_⟩
      · intro g hg
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, ← smul_add, hp g hg, smul_sub, smul_comm _ t⁻¹ p.1]
      · simp only [Prod.smul_fst]
        rw [smul_comm, ← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]
  choose P hPrel hPn using hplace
  by_cases hA : ∃ l0, E • (P l0).1 = 0 ∧ P l0 ≠ 0
  ·
    obtain ⟨l0, hEv, hP0⟩ := hA
    obtain ⟨φ, hφ⟩ := colHom_exists (V := V) e₁ δ D Kc k0 δx hδ 0
      (fun l => if l = l0 then δx • (P l).1 else 0)
      (fun l a => if l = l0 then (P l).2.1 a • s1 else 0)
      (fun l => if l = l0 then (P l).2.2 • η else 0)
      (by
        intro l; split_ifs with hl
        · subst hl; rw [smul_comm E δx, hEv, smul_zero]
        · exact smul_zero E)
      (by
        intro l a; split_ifs with hl
        · subst hl; rw [smul_comm e₁ ((P l).2.1 a) s1, he₁s1]
        · exact smul_zero e₁)
      (by
        intro l; split_ifs with hl
        · subst hl; rw [smul_comm E (P l).2.2 η, hEη, smul_comm (P l).2.2 δx η]
        · rw [smul_zero, smul_zero])
      (by
        intro l g hg
        split_ifs with hl
        · subst hl
          have hsum : ∀ a, Kc l a g • ((P l).2.1 a • s1) = (P l).2.1 a • (Kc l a g • s1) :=
            fun a => smul_comm _ _ _
          rw [LinearMap.zero_apply, zero_add]
          simp only [hsum]
          rw [smul_comm (k0 l g) (P l).2.2 η, hPrel l g hg, smul_sub,
            smul_comm ((((χ g)⁻¹ : T'ˣ) : T') • r g) δx (P l).1]
        · simp)
    refine ⟨φ, fun h0 => ?_⟩
    have key : ∀ x, colFreeMap (0 : Ymod r χ E →ₗ[A] V) (fun l => if l = l0 then δx • (P l).1 else 0)
        (fun l a => if l = l0 then (P l).2.1 a • s1 else 0)
        (fun l => if l = l0 then (P l).2.2 • η else 0) x = 0 := by
      intro x; rw [← hφ, h0, LinearMap.zero_apply]
    have hne : (P l0).1 ≠ 0 ∨ (∃ a, (P l0).2.1 a ≠ 0) ∨ (P l0).2.2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hP0 (Prod.ext hc.1 (Prod.ext (funext hc.2.1) hc.2.2))
    rcases hne with hv | ⟨a, ha⟩ | hc0
    · have := key (colGenJ 0 l0 1 0 0)
      simp only [colFreeMap_colGen] at this
      simp [hv, hδx] at this
    · have := key (colGenJ 0 l0 0 (Pi.single a 1) 0)
      simp only [colFreeMap_colGen] at this
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
        (fun h => absurd (Finset.mem_univ a) h)] at this
      simp [ha, hs10] at this
    · have := key (colGenJ 0 l0 0 0 1)
      simp only [colFreeMap_colGen] at this
      simp [hc0, hη0] at this
  ·
    push Not at hA
    have hEP : ∀ l, E • (P l).1 = η := by
      intro l
      rcases hPn l with ⟨h1, h2⟩ | h
      · exact absurd (hA l h1) h2
      · exact h
    let φY : Ymod r χ E →ₗ[A] V := (LinearMap.toSpanSingleton A V w0).comp (Ymod r χ E).subtype
    have hφY : ∀ g, φY ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ =
        ((((χ g)⁻¹ : T'ˣ) : T') • r g) • η - η := by
      intro g
      simp only [φY, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
        ycoc, mul_smul, hw0, sub_smul, one_smul]
    obtain ⟨φ, hφ⟩ := colHom_exists (V := V) e₁ δ D Kc k0 δx hδ φY
      (fun l => δx • (P l).1 - η)
      (fun l a => (P l).2.1 a • s1)
      (fun l => (P l).2.2 • η)
      (by intro l; rw [smul_sub, smul_comm E δx, hEP, hEη, sub_self])
      (by intro l a; rw [smul_comm e₁ ((P l).2.1 a) s1, he₁s1])
      (by intro l; rw [smul_comm E (P l).2.2 η, hEη, smul_comm (P l).2.2 δx η])
      (by
        intro l g hg
        have hsum : ∀ a, Kc l a g • ((P l).2.1 a • s1) = (P l).2.1 a • (Kc l a g • s1) :=
          fun a => smul_comm _ _ _
        rw [hφY]
        simp only [hsum]
        rw [smul_comm (k0 l g) (P l).2.2 η, hPrel l g hg, smul_sub, smul_sub,
          smul_comm ((((χ g)⁻¹ : T'ˣ) : T') • r g) δx (P l).1]
        abel)
    obtain ⟨g, hg⟩ := hfix η ⟨w0, by rw [DistribSMul.toLinearMap_apply, hw0]⟩ hη0
    refine ⟨φ, fun h0 => ?_⟩
    have := hφ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩, 0)
    rw [h0, LinearMap.zero_apply] at this
    simp only [colFreeMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Prod.fst_zero,
      Prod.snd_zero, zero_smul, Finset.sum_const_zero, add_zero, hφY] at this
    exact hg (sub_eq_zero.mp this.symm)

/- English proof (translation)
Introduce `O D M₁ M₂ M₂' N N' M₁'' M₂'' P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₂' ρN ρN' ρ₁'' ρ₂'' ρP β β' γ j ι π φ ψ CN2 CN CN' CP hβ hβ' hj hι hπ hφ hψ hcomp hγ hCP hH2 a b e ha hb he hc2 hc1`. Establish `hz : cup1 ρ₂ β a b ∈ characterColumnKernelPairSetVariant ρN`. Introduce `g h k`. Simplify using `only [cup1]`. Rewrite using `[← hβ g (a h) (ρ₂ h (b k)), ha g h, hb h k, map_mul, Module.End.mul_apply]`.

Simplify using `only [map_add, LinearMap.add_apply]`. Normalize the expressions using the abelian group laws. Take `⟨c, hcN, hc⟩` from `hH2 _ hz hc2 ⟨_, hc1, by`. Introduce `g h`. Simplify using `only [cup1, hcomp, map_neg]`.

Rewrite using `[hj g (b h), he h, ← hβ' g (a h) (ρ₂' h e), ha g h, map_mul, Module.End.mul_apply]`. Simplify using `only [map_sub, map_add, LinearMap.add_apply]`. Use the proof step `abel⟩`. Use `⟨fun g => ψ (c g), hCP _ hcN, ?_⟩` and prove the remaining obligations. Introduce `g h`.

Simplify using `only [cup1]`. Rewrite using `[← hφ g (b h), hγ, ← hψ g, ← map_sub, ← map_add]`. Conclude with `congrArg ψ (hc g h)`.
-/
theorem cupKillAdm : StatCupKillAdm := by
  intro O D M₁ M₂ M₂' N N' M₁'' M₂'' P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₂' ρN ρN' ρ₁'' ρ₂'' ρP
    β β' γ j ι π φ ψ CN2 CN CN' CP hβ hβ' hj hι hπ hφ hψ hcomp hγ hCP hH2 a b e ha hb he hc2 hc1
  have hz : cup1 ρ₂ β a b ∈ characterColumnKernelPairSetVariant ρN := by
    intro g h k
    simp only [cup1]
    rw [← hβ g (a h) (ρ₂ h (b k)), ha g h, hb h k, map_mul, Module.End.mul_apply]
    simp only [map_add, LinearMap.add_apply]
    abel
  obtain ⟨c, hcN, hc⟩ := hH2 _ hz hc2 ⟨_, hc1, by
    intro g h
    simp only [cup1, hcomp, map_neg]
    rw [hj g (b h), he h, ← hβ' g (a h) (ρ₂' h e), ha g h, map_mul, Module.End.mul_apply]
    simp only [map_sub, map_add, LinearMap.add_apply]
    abel⟩
  refine ⟨fun g => ψ (c g), hCP _ hcN, ?_⟩
  intro g h
  simp only [cup1]
  rw [← hφ g (b h), hγ, ← hψ g, ← map_sub, ← map_add]
  exact congrArg ψ (hc g h)

/- English proof (translation)
Introduce `R _ _ M _ _ g₀ n hn`. Set `f : (Fin g₀ → R) →ₗ[R] M` to `{ toFun := fun c => ∑ i, c i • n i map_add' := fun x y => by`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun r x => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }`.

Establish `hsurj : Function.Surjective f`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hn, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `⟨Pi.single i 1, ?_⟩` and prove the remaining obligations. Simplify using `[f, Pi.single_apply]`.

Take `⟨m, s, hs⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (LinearMap.ker f))`. Use `⟨m, Matrix.of s, ⟨?_⟩⟩` and prove the remaining obligations. Establish `hrel : relSpan (Matrix.of s) = LinearMap.ker f`. Rewrite using `[relSpan, ← hs]`. Both sides reduce to the same expression.

Conclude with `((Submodule.quotEquivOfEq _ _ hrel).trans (f.quotKerEquivOfSurjective hsurj)).symm`.
-/
theorem finPres : StatFinPres := by
  intro R _ _ M _ _ g₀ n hn
  classical
  let f : (Fin g₀ → R) →ₗ[R] M :=
    { toFun := fun c => ∑ i, c i • n i
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hn, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [f, Pi.single_apply]
  obtain ⟨m, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (LinearMap.ker f))
  refine ⟨m, Matrix.of s, ⟨?_⟩⟩
  have hrel : relSpan (Matrix.of s) = LinearMap.ker f := by
    rw [relSpan, ← hs]
    rfl
  exact ((Submodule.quotEquivOfEq _ _ hrel).trans (f.quotKerEquivOfSurjective hsurj)).symm

end Formalism.NG
