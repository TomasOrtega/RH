import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
Take `⟨u, hu, k, hk, l, hl, he⟩` from `F.fact _ h`. Rewrite `hu`, `hk`, `hl` using `[Subgroup.mem_inf]`. Establish `hyl : y * l * y⁻¹ ∈ F.Lf` using `F.M_L y hy l hl.1`. Establish `key : (x⁻¹ * u) * (k * y⁻¹) * (y * l * y⁻¹) = 1`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨h1, h2⟩` from `F.uniq _ (F.Uf.mul_mem (F.Uf.inv_mem hx) hu.1) _ (F.Mf.mul_mem hk.1 (F.Mf.inv_mem hy)) _ hyl key`. Establish `hxu : x = u` using `inv_mul_eq_one.mp h1`. Establish `hyk : y = k` using `(mul_inv_eq_one.mp h2).symm`. Conclude with `⟨hxu ▸ hu.2, hyk ▸ hk.2⟩`.
-/
private theorem leviSum_split {G : Type} [Group G] {I : Subgroup G} (F : LeviFact I) {x y : G}
    (hx : x ∈ F.Uf) (hy : y ∈ F.Mf) (h : x * y ∈ I) : x ∈ I ∧ y ∈ I := by
  obtain ⟨u, hu, k, hk, l, hl, he⟩ := F.fact _ h
  rw [Subgroup.mem_inf] at hu hk hl
  have hyl : y * l * y⁻¹ ∈ F.Lf := F.M_L y hy l hl.1
  have key : (x⁻¹ * u) * (k * y⁻¹) * (y * l * y⁻¹) = 1 := by
    calc (x⁻¹ * u) * (k * y⁻¹) * (y * l * y⁻¹) = x⁻¹ * (u * k * l) * y⁻¹ := by group
      _ = 1 := by rw [← he]; group
  obtain ⟨h1, h2⟩ := F.uniq _ (F.Uf.mul_mem (F.Uf.inv_mem hx) hu.1) _
    (F.Mf.mul_mem hk.1 (F.Mf.inv_mem hy)) _ hyl key
  have hxu : x = u := inv_mul_eq_one.mp h1
  have hyk : y = k := (mul_inv_eq_one.mp h2).symm
  exact ⟨hxu ▸ hu.2, hyk ▸ hk.2⟩

/- English proof (translation)
Introduce `G _ I F m _ hm s hs hs1 r hr q`. Establish `hmM : m ∈ F.Mf` using `hm.1`. Establish `hsm : ∀ (g : I) (x : G), g • (x : G ⧸ I) = (((g : G) * x : G) : G ⧸ I)` using `fun g x => rfl`. Establish `huniq : ∀ a ∈ s, ∀ a' ∈ s, ∀ v ∈ r a, ∀ v' ∈ r a', ((v' * a' : G) : G ⧸ I) = ((v * a : G) : G ⧸ I) → a' = a ∧ v' = v`. Introduce `a ha a' ha' v hv v' hv' heq`.

Establish `hvI` using `Subgroup.mem_inf.mp ((hr a ha).1 v hv)`. Establish `hv'I` using `Subgroup.mem_inf.mp ((hr a' ha').1 v' hv')`. Establish `hd : (v * a)⁻¹ * (v' * a') ∈ I` using `QuotientGroup.eq.mp heq.symm`. Take `⟨j, hj, j', hj', hja⟩` from `hs a ha`. Take `⟨j1, hj1, j1', hj1', hja'⟩` from `hs a' ha'`.

Rewrite `hj`, `hj'`, `hj1`, `hj1'` using `[Subgroup.mem_inf]`. Establish `hw : j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹ ∈ F.Uf` using `F.M_U _ (F.Mf.inv_mem hj.1) _ (F.Uf.mul_mem (F.Uf.inv_mem hvI.1) hv'I.1)`. Establish `hX : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ ∈ F.Uf` using `F.M_U _ (F.Mf.inv_mem hmM) _ hw`. Establish `hY : m⁻¹ * (j⁻¹ * j1) * m ∈ F.Mf` using `F.Mf.mul_mem (F.Mf.mul_mem (F.Mf.inv_mem hmM) (F.Mf.mul_mem (F.Mf.inv_mem hj.1) hj1.1)) hmM`. Establish `hXY : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m) ∈ I`.

Establish `he : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m) = j' * ((v * a)⁻¹ * (v' * a')) * j1'⁻¹`. Rewrite using `[hja, hja']`. Use `group`. Rewrite using `[he]`. Conclude with `I.mul_mem (I.mul_mem hj'.2 hd) (I.inv_mem hj1'.2)`.

Establish `hYI` using `(leviSum_split F hX hY hXY).2`. Establish `haa : a' = a`. Use `(hs1 j1 (Subgroup.mem_inf.mpr hj1)).unique ⟨ha', ?_⟩ ⟨ha, ?_⟩` and prove the remaining obligations. Establish `he : a'⁻¹ * (j1 * m) = j1'⁻¹`. Rewrite using `[hja']`.

Use `group`. Rewrite using `[he]`. Conclude with `I.inv_mem hj1'.2`. Establish `he : a⁻¹ * (j1 * m) = j'⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m)`. Rewrite using `[hja]`.

Use `group`. Rewrite using `[he]`. Conclude with `I.mul_mem (I.inv_mem hj'.2) hYI`. Substitute `haa` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations.

Use `((hr a' ha).2 v' (Subgroup.mem_inf.mpr hv'I)).unique ⟨hv', ?_⟩ ⟨hv, ?_⟩` and prove the remaining obligations. Establish `he : a'⁻¹ * (v'⁻¹ * v') * a' = 1` using `by group`. Rewrite using `[he]`. Conclude with `I.one_mem`. Establish `he : a'⁻¹ * (v⁻¹ * v') * a' = (v * a')⁻¹ * (v' * a')` using `by group`.

Rewrite using `[he]`. Conclude with `hd`. Prove the components needed by the constructor for the conclusion. Introduce `hq`. Take `⟨⟨i, hi⟩, rfl⟩` from `MulAction.mem_orbit_iff.mp hq`.

Take `⟨u', hu', j, hj, l, hl, hil⟩` from `F.fact i hi`. Take `⟨a, ⟨ha, hajm⟩, -⟩` from `hs1 j hj`. Take `⟨v, ⟨hv, hvu⟩, -⟩` from `(hr a ha).2 u' hu'`. Rewrite `hl`, `hj`, `hu'` using `[Subgroup.mem_inf]`. Establish `hq : (⟨i, hi⟩ : I) • (m : G ⧸ I) = ((v * a : G) : G ⧸ I)`.

Rewrite using `[hsm]`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Establish `he : ((i : G) * m)⁻¹ * (v * a) = (m⁻¹ * l * m)⁻¹ * (a⁻¹ * (j * m))⁻¹ * (a⁻¹ * (v⁻¹ * u') * a)⁻¹`. Simplify using `only [hil]`. Use `group`.

Rewrite using `[he]`. Conclude with `I.mul_mem (I.mul_mem (I.inv_mem (hm.2.2 l (Subgroup.mem_inf.mpr hl))) (I.inv_mem hajm)) (I.inv_mem hvu)`. Rewrite using `[hq]`. Use `⟨(a, v), ⟨ha, hv, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `p' hp1 hp2 hp3`.

Take `⟨h1, h2⟩` from `huniq a ha p'.1 hp1 v hv p'.2 hp2 hp3`. Conclude with `Prod.ext h1 h2`. Introduce and unpack `⟨⟨a, v⟩, ⟨ha, hv, rfl⟩, -⟩`. Take `⟨j, hj, j', hj', hja⟩` from `hs a ha`. Establish `hvI` using `Subgroup.mem_inf.mp ((hr a ha).1 v hv)`.

Rewrite `hj`, `hj'` using `[Subgroup.mem_inf]`. Apply `MulAction.mem_orbit_iff.mpr` to reduce the goal to its premises. Use `⟨⟨v * j, I.mul_mem hvI.2 hj.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hsm]`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises.

Establish `he : ((v * j : G) * m)⁻¹ * (v * a) = j'`. Rewrite using `[hja]`. Use `group`. Simplify using `only [he]`. Conclude with `hj'.2`.
-/
theorem UpperTheory.V.AlgebraTools.leviSum :
    ∀ (G : Type) [Group G] (I : Subgroup G) (F : LeviFact I) (m : G), HeckePair I → F.Pos m → ∀ (s : Finset G), (∀ a ∈ s, ∃ j ∈ F.Mf ⊓ I, ∃ j' ∈ F.Mf ⊓ I, a = j * m * j') → (∀ j ∈ F.Mf ⊓ I, ∃! a, a ∈ s ∧ a⁻¹ * (j * m) ∈ I) → ∀ (r : G → Finset G), (∀ a ∈ s, (∀ u ∈ r a, u ∈ F.Uf ⊓ I) ∧ ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ r a ∧ a⁻¹ * (u⁻¹ * x) * a ∈ I) → ∀ q : G ⧸ I, q ∈ MulAction.orbit I (m : G ⧸ I) ↔ ∃ p : G × G, (p.1 ∈ s ∧ p.2 ∈ r p.1 ∧ ((p.2 * p.1 : G) : G ⧸ I) = q) ∧ ∀ p' : G × G, p'.1 ∈ s → p'.2 ∈ r p'.1 → ((p'.2 * p'.1 : G) : G ⧸ I) = q → p' = p := by
  intro G _ I F m _ hm s hs hs1 r hr q
  have hmM : m ∈ F.Mf := hm.1
  have hsm : ∀ (g : I) (x : G), g • (x : G ⧸ I) = (((g : G) * x : G) : G ⧸ I) := fun g x => rfl
  have huniq : ∀ a ∈ s, ∀ a' ∈ s, ∀ v ∈ r a, ∀ v' ∈ r a',
      ((v' * a' : G) : G ⧸ I) = ((v * a : G) : G ⧸ I) → a' = a ∧ v' = v := by
    intro a ha a' ha' v hv v' hv' heq
    have hvI := Subgroup.mem_inf.mp ((hr a ha).1 v hv)
    have hv'I := Subgroup.mem_inf.mp ((hr a' ha').1 v' hv')
    have hd : (v * a)⁻¹ * (v' * a') ∈ I := QuotientGroup.eq.mp heq.symm
    obtain ⟨j, hj, j', hj', hja⟩ := hs a ha
    obtain ⟨j1, hj1, j1', hj1', hja'⟩ := hs a' ha'
    rw [Subgroup.mem_inf] at hj hj' hj1 hj1'
    have hw : j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹ ∈ F.Uf :=
      F.M_U _ (F.Mf.inv_mem hj.1) _ (F.Uf.mul_mem (F.Uf.inv_mem hvI.1) hv'I.1)
    have hX : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ ∈ F.Uf :=
      F.M_U _ (F.Mf.inv_mem hmM) _ hw
    have hY : m⁻¹ * (j⁻¹ * j1) * m ∈ F.Mf :=
      F.Mf.mul_mem (F.Mf.mul_mem (F.Mf.inv_mem hmM) (F.Mf.mul_mem (F.Mf.inv_mem hj.1) hj1.1)) hmM
    have hXY : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m) ∈ I := by
      have he : m⁻¹ * (j⁻¹ * (v⁻¹ * v') * j⁻¹⁻¹) * m⁻¹⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m)
          = j' * ((v * a)⁻¹ * (v' * a')) * j1'⁻¹ := by
        rw [hja, hja']
        group
      rw [he]
      exact I.mul_mem (I.mul_mem hj'.2 hd) (I.inv_mem hj1'.2)
    have hYI := (leviSum_split F hX hY hXY).2
    have haa : a' = a := by
      refine (hs1 j1 (Subgroup.mem_inf.mpr hj1)).unique ⟨ha', ?_⟩ ⟨ha, ?_⟩
      · have he : a'⁻¹ * (j1 * m) = j1'⁻¹ := by
          rw [hja']
          group
        rw [he]
        exact I.inv_mem hj1'.2
      · have he : a⁻¹ * (j1 * m) = j'⁻¹ * (m⁻¹ * (j⁻¹ * j1) * m) := by
          rw [hja]
          group
        rw [he]
        exact I.mul_mem (I.inv_mem hj'.2) hYI
    subst haa
    refine ⟨rfl, ?_⟩
    refine ((hr a' ha).2 v' (Subgroup.mem_inf.mpr hv'I)).unique ⟨hv', ?_⟩ ⟨hv, ?_⟩
    · have he : a'⁻¹ * (v'⁻¹ * v') * a' = 1 := by group
      rw [he]
      exact I.one_mem
    · have he : a'⁻¹ * (v⁻¹ * v') * a' = (v * a')⁻¹ * (v' * a') := by group
      rw [he]
      exact hd
  constructor
  · intro hq
    obtain ⟨⟨i, hi⟩, rfl⟩ := MulAction.mem_orbit_iff.mp hq
    obtain ⟨u', hu', j, hj, l, hl, hil⟩ := F.fact i hi
    obtain ⟨a, ⟨ha, hajm⟩, -⟩ := hs1 j hj
    obtain ⟨v, ⟨hv, hvu⟩, -⟩ := (hr a ha).2 u' hu'
    rw [Subgroup.mem_inf] at hl hj hu'
    have hq : (⟨i, hi⟩ : I) • (m : G ⧸ I) = ((v * a : G) : G ⧸ I) := by
      rw [hsm]
      apply QuotientGroup.eq.mpr
      have he : ((i : G) * m)⁻¹ * (v * a)
          = (m⁻¹ * l * m)⁻¹ * (a⁻¹ * (j * m))⁻¹ * (a⁻¹ * (v⁻¹ * u') * a)⁻¹ := by
        simp only [hil]
        group
      rw [he]
      exact I.mul_mem (I.mul_mem (I.inv_mem (hm.2.2 l (Subgroup.mem_inf.mpr hl)))
        (I.inv_mem hajm)) (I.inv_mem hvu)
    rw [hq]
    refine ⟨(a, v), ⟨ha, hv, rfl⟩, ?_⟩
    intro p' hp1 hp2 hp3
    obtain ⟨h1, h2⟩ := huniq a ha p'.1 hp1 v hv p'.2 hp2 hp3
    exact Prod.ext h1 h2
  · rintro ⟨⟨a, v⟩, ⟨ha, hv, rfl⟩, -⟩
    obtain ⟨j, hj, j', hj', hja⟩ := hs a ha
    have hvI := Subgroup.mem_inf.mp ((hr a ha).1 v hv)
    rw [Subgroup.mem_inf] at hj hj'
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨v * j, I.mul_mem hvI.2 hj.2⟩, ?_⟩
    rw [hsm]
    apply QuotientGroup.eq.mpr
    have he : ((v * j : G) * m)⁻¹ * (v * a) = j' := by
      rw [hja]
      group
    simp only [he]
    exact hj'.2
