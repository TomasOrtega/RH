import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviSum
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

/- English proof (translation)
Set `φ : G → G ⧸ K'` to `fun x => ((x * m : G) : G ⧸ K')`. Establish `h1 : (φ '' (S : Set G)).Finite`. Use `Set.Finite.subset hfin ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨⟨x, hS hx⟩, rfl⟩`.

Take `⟨t, ht, hb⟩` from `Set.exists_subset_bijOn (S : Set G) φ`. Establish `h2 : t.Finite` using `(hb.finite_iff_finite).2 h1`. Use `⟨h2.toFinset, fun u hu => ht (h2.mem_toFinset.1 hu), fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, e⟩` from `hb.surjOn ⟨x, hx, rfl⟩`. Use `⟨u, ⟨h2.mem_toFinset.2 hu, QuotientGroup.eq.1 e⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `u' ⟨hu', e'⟩`. Conclude with `hb.injOn (h2.mem_toFinset.1 hu') hu ((QuotientGroup.eq.2 e').trans e.symm)`.
-/
private theorem leviLevel_reps {G : Type} [Group G] {K K' : Subgroup G} (S : Subgroup G) {m : G} (hS : S ≤ K)
    (hfin : FinOrb K K' m) :
    ∃ r : Finset G, (∀ u ∈ r, u ∈ S) ∧ ∀ x ∈ S, ∃! u, u ∈ r ∧ (u * m)⁻¹ * (x * m) ∈ K' := by
  classical
  let φ : G → G ⧸ K' := fun x => ((x * m : G) : G ⧸ K')
  have h1 : (φ '' (S : Set G)).Finite := by
    refine Set.Finite.subset hfin ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hS hx⟩, rfl⟩
  obtain ⟨t, ht, hb⟩ := Set.exists_subset_bijOn (S : Set G) φ
  have h2 : t.Finite := (hb.finite_iff_finite).2 h1
  refine ⟨h2.toFinset, fun u hu => ht (h2.mem_toFinset.1 hu), fun x hx => ?_⟩
  obtain ⟨u, hu, e⟩ := hb.surjOn ⟨x, hx, rfl⟩
  refine ⟨u, ⟨h2.mem_toFinset.2 hu, QuotientGroup.eq.1 e⟩, ?_⟩
  rintro u' ⟨hu', e'⟩
  exact hb.injOn (h2.mem_toFinset.1 hu') hu ((QuotientGroup.eq.2 e').trans e.symm)

/- English proof (translation)
Establish `hinj : ∀ u ∈ r, ∀ u' ∈ r, ((f u * m : G) : G ⧸ K') = ((f u' * m : G) : G ⧸ K') → u = u'` using `fun u hu u' hu' e => (hr _ (hf u' hu')).unique ⟨hu, QuotientGroup.eq.1 e⟩ ⟨hu', by simp⟩`. Rewrite using `[(UpperTheory.V.AlgebraTools.hkApply A G M ρ K K' m hfin).2.1 (r.image fun u => f u * m) ?_ ?_ v, Finset.sum_image]`. Introduce `u hu u' hu' e`. Conclude with `hinj u hu u' hu' (congrArg _ e)`. Introduce `y hy`.

Take `⟨u, hu, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `⟨⟨f u, hS (hf u hu)⟩, rfl⟩`. Introduce and unpack `_ ⟨⟨g, hgK⟩, rfl⟩`. Take `⟨x, hx, e⟩` from `hg g hgK`. Take `⟨u, ⟨hu, e'⟩, -⟩` from `hr x hx`.

Establish `e2 : ((f u * m : G) : G ⧸ K') = ((g * m : G) : G ⧸ K')` using `(QuotientGroup.eq.2 e').trans (QuotientGroup.eq.2 e)`. Use `⟨f u * m, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e2⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨hy, e3⟩`. Take `⟨u', hu', rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[hinj u' hu' u hu (e3.trans e2.symm)]`.
-/
private theorem leviLevel_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) {K K' : Subgroup G} (S : Subgroup G) {m : G} (hS : S ≤ K) (hfin : FinOrb K K' m)
    (hg : ∀ g ∈ K, ∃ x ∈ S, (x * m)⁻¹ * (g * m) ∈ K') (r : Finset G) (f : G → G) (hf : ∀ u ∈ r, f u ∈ S)
    (hr : ∀ x ∈ S, ∃! u, u ∈ r ∧ (f u * m)⁻¹ * (x * m) ∈ K') (v : fixd ρ K') :
    (hk2 ρ K K' m v : M) = ∑ u ∈ r, ρ (f u * m) v := by
  classical
  have hinj : ∀ u ∈ r, ∀ u' ∈ r, ((f u * m : G) : G ⧸ K') = ((f u' * m : G) : G ⧸ K') → u = u' :=
    fun u hu u' hu' e => (hr _ (hf u' hu')).unique ⟨hu, QuotientGroup.eq.1 e⟩ ⟨hu', by simp⟩
  rw [(UpperTheory.V.AlgebraTools.hkApply A G M ρ K K' m hfin).2.1 (r.image fun u => f u * m) ?_ ?_ v, Finset.sum_image]
  · intro u hu u' hu' e
    exact hinj u hu u' hu' (congrArg _ e)
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨⟨f u, hS (hf u hu)⟩, rfl⟩
  · rintro _ ⟨⟨g, hgK⟩, rfl⟩
    obtain ⟨x, hx, e⟩ := hg g hgK
    obtain ⟨u, ⟨hu, e'⟩, -⟩ := hr x hx
    have e2 : ((f u * m : G) : G ⧸ K') = ((g * m : G) : G ⧸ K') :=
      (QuotientGroup.eq.2 e').trans (QuotientGroup.eq.2 e)
    refine ⟨f u * m, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e2⟩, ?_⟩
    rintro y ⟨hy, e3⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
    rw [hinj u' hu' u hu (e3.trans e2.symm)]

/- English proof (translation)
Introduce `g hg`. Take `⟨u, hu, j, hj, l, hl, rfl⟩` from `F.fact g hg`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Establish `e : (u * m)⁻¹ * (u * j * l * m) = m⁻¹ * (j * m) * (m⁻¹ * l * m)` using `by group`. Rewrite using `[e, ← hJ j hj, inv_mul_cancel_left]`.

Conclude with `mul_mem hj.2 (hL l hl)`.
-/
private theorem leviLevel_cover {G : Type} [Group G] {K : Subgroup G} (F : LeviFact K) {m : G}
    (hL : ∀ l ∈ F.Lf ⊓ K, m⁻¹ * l * m ∈ K) (hJ : ∀ j ∈ F.Mf ⊓ K, m * j = j * m) :
    ∀ g ∈ K, ∃ x ∈ F.Uf ⊓ K, (x * m)⁻¹ * (g * m) ∈ K := by
  intro g hg
  obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
  refine ⟨u, hu, ?_⟩
  have e : (u * m)⁻¹ * (u * j * l * m) = m⁻¹ * (j * m) * (m⁻¹ * l * m) := by group
  rw [e, ← hJ j hj, inv_mul_cancel_left]
  exact mul_mem hj.2 (hL l hl)

/- English proof (translation)
Introduce `A G M _ _ _ _ ρ I I' h F F' m hI hI' h1 eU eM eL hU hL hn hm hJ`. Take `⟨r, hr, hr2⟩` from `leviLevel_reps (F.Uf ⊓ I) inf_le_right (hI m)`. Take `⟨t, ht, ht2⟩` from `leviLevel_reps (F.Mf ⊓ I) inf_le_right h1`. Establish `cI` using `leviLevel_cover F hm.2.2 hJ`. Establish `cI' : ∀ g ∈ I', ∃ x ∈ F.Uf ⊓ I, (x * m)⁻¹ * (g * m) ∈ I'`.

Introduce `g hg`. Take `⟨x, hx, e⟩` from `leviLevel_cover F' (m := m) (fun l hl => by`. Establish `hl1 : l ∈ F.Lf` using `eL ▸ hl.1`. Use `hL ⟨?_, hm.2.2 l ⟨hl1, h hl.2⟩⟩` and prove the remaining obligations. Simplify using `using F.M_L _ (inv_mem hm.1) l hl1) (fun j hj => hJ j ⟨eM ▸ hj.1, h hj.2⟩) g hg`.

Conclude with `⟨x, ⟨eU ▸ hx.1, h hx.2⟩, e⟩`. Establish `cJ : ∀ g ∈ I, ∃ x ∈ F.Mf ⊓ I, (x * 1)⁻¹ * (g * 1) ∈ I'`. Introduce `g hg`. Take `⟨u, hu, j, hj, l, hl, rfl⟩` from `F.fact g hg`. Use `⟨j, hj, ?_⟩` and prove the remaining obligations.

Use `mul_mem (hn _ (I.inv_mem hj.2) _ (hU hu)) (hL hl)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `hr3 : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ r ∧ (u * m)⁻¹ * (x * m) ∈ I'`. Introduce `x hx`.

Take `⟨u, ⟨hu, e⟩, huq⟩` from `hr2 x hx`. Use `⟨u, ⟨hu, hU ⟨?_, e⟩⟩, fun u' hu' => huq u' ⟨hu'.1, h hu'.2⟩⟩` and prove the remaining obligations. Use `F.M_U _ (inv_mem hm.1) _ (mul_mem (inv_mem (hr u hu).1) hx.1)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `show _ ∈ F.Uf ↔ _`.

Use `congr! 1`. Use `group`. Establish `sI` using `leviLevel_sum ρ (F.Uf ⊓ I) inf_le_right (hI m) cI r id hr hr2`. Establish `sJ` using `leviLevel_sum ρ (F.Mf ⊓ I) inf_le_right h1 cJ t id ht ht2`. Establish `sI' : ∀ j ∈ F.Mf ⊓ I, ∀ v : fixd ρ I', (hk2 ρ I' I' m v : M) = ∑ u ∈ r, ρ (j⁻¹ * u * j * m) v`.

Introduce `j hj`. Establish `hc : ∀ a ∈ F.Mf ⊓ I, ∀ x ∈ F.Uf ⊓ I, a * x * a⁻¹ ∈ F.Uf ⊓ I` using `fun a ha x hx => ⟨F.M_U a ha.1 x hx.1, I.mul_mem (I.mul_mem ha.2 hx.2) (I.inv_mem ha.2)⟩`. Use `leviLevel_sum ρ (F.Uf ⊓ I) hU (hI' m) cI' r (fun u => j⁻¹ * u * j) (fun u hu => ?_) (fun x hx => ?_)` and prove the remaining obligations. Simplify using `using hc _ (inv_mem hj) u (hr u hu)`. Use `(existsUnique_congr fun u => and_congr_right fun _ => ?_).1 (hr3 _ (hc j hj x hx))` and prove the remaining obligations.

Establish `e : j * ((j⁻¹ * u * j * m)⁻¹ * (x * m)) * j⁻¹ = (u * m)⁻¹ * (j * x * j⁻¹ * m)`. Establish `e1 : j * m⁻¹ * j⁻¹ = m⁻¹`. Rewrite using `[mul_assoc, ← _root_.mul_inv_rev, ← hJ j hj]`. Use `group`. Establish `e2 : m * j⁻¹ = j⁻¹ * m` using `hJ _ (inv_mem hj)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← e]`. Use `⟨fun hx => ?_, hn _ hj.2 _⟩` and prove the remaining obligations. Use `hn _ (I.inv_mem hj.2) _ hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `group`. Use `⟨LinearMap.ext fun v => Subtype.ext ?_, LinearMap.ext fun v => Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (hk2 ρ I' I' m (inc ρ h v) : M) = hk2 ρ I I m v`. Rewrite using `[sI' 1 (one_mem _), sI]`. Simplify using `only [inv_one, one_mul, mul_one, id]`.

Both sides reduce to the same expression. Use `show (hk2 ρ I I' 1 (hk2 ρ I' I' m v) : M) = hk2 ρ I I m (hk2 ρ I I' 1 v)`. Rewrite using `[sJ, sI, sJ]`. Simplify using `only [id, mul_one, map_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[sI' j (ht j hj), map_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc u, hJ j (ht j hj)]`. Use `congr 2`.

Use `group`.
-/
theorem UpperTheory.V.AlgebraTools.leviLevel :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I I' : Subgroup G) (h : I' ≤ I) (F : LeviFact I) (F' : LeviFact I') (m : G), HeckePair I → HeckePair I' → FinOrb I I' 1 → F'.Uf = F.Uf → F'.Mf = F.Mf → F'.Lf = F.Lf → F.Uf ⊓ I ≤ I' → F.Lf ⊓ I ≤ I' → (∀ a ∈ I, ∀ b ∈ I', a * b * a⁻¹ ∈ I') → F.Pos m → (∀ j ∈ F.Mf ⊓ I, m * j = j * m) → hk ρ I' m ∘ₗ inc ρ h = inc ρ h ∘ₗ hk ρ I m ∧ trc ρ I I' ∘ₗ hk ρ I' m = hk ρ I m ∘ₗ trc ρ I I' := by
  intro A G M _ _ _ _ ρ I I' h F F' m hI hI' h1 eU eM eL hU hL hn hm hJ
  obtain ⟨r, hr, hr2⟩ := leviLevel_reps (F.Uf ⊓ I) inf_le_right (hI m)
  obtain ⟨t, ht, ht2⟩ := leviLevel_reps (F.Mf ⊓ I) inf_le_right h1
  have cI := leviLevel_cover F hm.2.2 hJ
  have cI' : ∀ g ∈ I', ∃ x ∈ F.Uf ⊓ I, (x * m)⁻¹ * (g * m) ∈ I' := by
    intro g hg
    obtain ⟨x, hx, e⟩ := leviLevel_cover F' (m := m) (fun l hl => by
      have hl1 : l ∈ F.Lf := eL ▸ hl.1
      refine hL ⟨?_, hm.2.2 l ⟨hl1, h hl.2⟩⟩
      simpa using F.M_L _ (inv_mem hm.1) l hl1) (fun j hj => hJ j ⟨eM ▸ hj.1, h hj.2⟩) g hg
    exact ⟨x, ⟨eU ▸ hx.1, h hx.2⟩, e⟩
  have cJ : ∀ g ∈ I, ∃ x ∈ F.Mf ⊓ I, (x * 1)⁻¹ * (g * 1) ∈ I' := by
    intro g hg
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
    refine ⟨j, hj, ?_⟩
    have := mul_mem (hn _ (I.inv_mem hj.2) _ (hU hu)) (hL hl)
    convert this using 1
    group
  have hr3 : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ r ∧ (u * m)⁻¹ * (x * m) ∈ I' := by
    intro x hx
    obtain ⟨u, ⟨hu, e⟩, huq⟩ := hr2 x hx
    refine ⟨u, ⟨hu, hU ⟨?_, e⟩⟩, fun u' hu' => huq u' ⟨hu'.1, h hu'.2⟩⟩
    have := F.M_U _ (inv_mem hm.1) _ (mul_mem (inv_mem (hr u hu).1) hx.1)
    convert this using 1
    show _ ∈ F.Uf ↔ _
    congr! 1
    group
  have sI := leviLevel_sum ρ (F.Uf ⊓ I) inf_le_right (hI m) cI r id hr hr2
  have sJ := leviLevel_sum ρ (F.Mf ⊓ I) inf_le_right h1 cJ t id ht ht2
  have sI' : ∀ j ∈ F.Mf ⊓ I, ∀ v : fixd ρ I',
      (hk2 ρ I' I' m v : M) = ∑ u ∈ r, ρ (j⁻¹ * u * j * m) v := by
    intro j hj
    have hc : ∀ a ∈ F.Mf ⊓ I, ∀ x ∈ F.Uf ⊓ I, a * x * a⁻¹ ∈ F.Uf ⊓ I := fun a ha x hx =>
      ⟨F.M_U a ha.1 x hx.1, I.mul_mem (I.mul_mem ha.2 hx.2) (I.inv_mem ha.2)⟩
    refine leviLevel_sum ρ (F.Uf ⊓ I) hU (hI' m) cI' r (fun u => j⁻¹ * u * j) (fun u hu => ?_) (fun x hx => ?_)
    · simpa using hc _ (inv_mem hj) u (hr u hu)
    · refine (existsUnique_congr fun u => and_congr_right fun _ => ?_).1 (hr3 _ (hc j hj x hx))
      have e : j * ((j⁻¹ * u * j * m)⁻¹ * (x * m)) * j⁻¹ = (u * m)⁻¹ * (j * x * j⁻¹ * m) := by
        have e1 : j * m⁻¹ * j⁻¹ = m⁻¹ := by
          rw [mul_assoc, ← _root_.mul_inv_rev, ← hJ j hj]; group
        have e2 : m * j⁻¹ = j⁻¹ * m := hJ _ (inv_mem hj)
        calc _ = (j * m⁻¹ * j⁻¹) * u⁻¹ * j * x * (m * j⁻¹) := by group
          _ = _ := by rw [e1, e2]; group
      rw [← e]
      refine ⟨fun hx => ?_, hn _ hj.2 _⟩
      have := hn _ (I.inv_mem hj.2) _ hx
      convert this using 1
      group
  refine ⟨LinearMap.ext fun v => Subtype.ext ?_, LinearMap.ext fun v => Subtype.ext ?_⟩
  · show (hk2 ρ I' I' m (inc ρ h v) : M) = hk2 ρ I I m v
    rw [sI' 1 (one_mem _), sI]
    simp only [inv_one, one_mul, mul_one, id]
    rfl
  · show (hk2 ρ I I' 1 (hk2 ρ I' I' m v) : M) = hk2 ρ I I m (hk2 ρ I I' 1 v)
    rw [sJ, sI, sJ]
    simp only [id, mul_one, map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [sI' j (ht j hj), map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc u, hJ j (ht j hj)]
    congr 2
    group
