import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

/- English proof (translation)
Establish `hs : Function.support (fun c : G ⧸ K => u c.out • (ρ c.out ∘ₗ LinearMap.id)) ⊆ (S : Set (G ⧸ K))`. Introduce `c hc`. Use `Finset.mem_coe.2 (hS c fun h0 => hc ?_)` and prove the remaining obligations. Simplify using `[h0]`. Simplify using `only [Lv, GlobalTheory.BCT.levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]`.

Rewrite using `[finsum_eq_sum_of_support_subset _ hs]`. Both sides reduce to the same expression.
-/
private lemma lv_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (u : G → ℂ) (S : Finset (G ⧸ K)) (hS : ∀ c : G ⧸ K, u c.out ≠ 0 → c ∈ S) :
    Lv ρ K u = ∑ c ∈ S, u c.out • ρ c.out := by
  have hs : Function.support (fun c : G ⧸ K => u c.out • (ρ c.out ∘ₗ LinearMap.id)) ⊆ (S : Set (G ⧸ K)) := by
    intro c hc
    refine Finset.mem_coe.2 (hS c fun h0 => hc ?_)
    simp [h0]
  simp only [Lv, GlobalTheory.BCT.levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  rw [finsum_eq_sum_of_support_subset _ hs]
  rfl

/- English proof (translation)
Introduce `G A V _ _ _ _ ρ K N j q f h h₁ hqj hcomm hjN hqK hh hh₁N hK hfN hfs hh₁s y hy`. Establish `hyk : ∀ k ∈ K, ρ k y = y` using `fun k hk => by`. Use `hy ⟨k, hk⟩` as an intermediate fact. Simplify using `using this`. Establish `hx0 : ∀ g, q ((j (q g))⁻¹ * g) = 1` using `fun g => by simp [hqj]`.

Establish `hright : ∀ g k, k ∈ K → h (g * k) = h g`. Introduce `g k hk`. Rewrite using `[hh (g * k), hh g]`. Establish `e1 : f (q (g * k)) = f (q g)`. Rewrite using `[map_mul]`.

Conclude with `hfN _ (hqK k hk) _`. Establish `c : Commute (j (q k)) ((j (q g))⁻¹ * g)` using `hcomm (q k) _ (hx0 g)`. Establish `e2 : (j (q (g * k)))⁻¹ * (g * k) = ((j (q g))⁻¹ * g) * ((j (q k))⁻¹ * k)`. Establish `c' : (j (q k))⁻¹ * ((j (q g))⁻¹ * g) = ((j (q g))⁻¹ * g) * (j (q k))⁻¹` using `c.inv_left.eq`. Rewrite using `[map_mul, map_mul, mul_inv_rev, ← mul_assoc ((j (q g))⁻¹ * g), ← c']`.

Simplify using `only [mul_assoc]`. Rewrite using `[e1, e2, (hK _ (K.mul_mem (K.inv_mem (hjN _ (hqK k hk))) hk) _).2]`. Use `set S₁ : Finset (A ⧸ N) := hfs.toFinset with hS₁`. Use `set S₂ : Finset (G ⧸ K) := hh₁s.toFinset with hS₂`. Establish `m₁ : ∀ s, s ∈ S₁ ↔ f s.out ≠ 0` using `fun s => by simp [hS₁]`.

Establish `m₂ : ∀ t, t ∈ S₂ ↔ h₁ t.out ≠ 0` using `fun t => by simp [hS₂]`. Set `φ : (A ⧸ N) × (G ⧸ K) → G ⧸ K` to `fun p => ((j p.1.out * p.2.out : G) : G ⧸ K)`. Establish `hterm : ∀ (s : A ⧸ N) (t : G ⧸ K), t ∈ S₂ → h (j s.out * t.out) = f s.out * h₁ t.out`. Introduce `s t ht`. Establish `hn : q t.out ∈ N` using `hh₁N _ ((m₂ t).1 ht)`.

Establish `e0 : q (j s.out * t.out) = s.out * q t.out` using `by rw [map_mul, hqj]`. Establish `e1 : (j (q (j s.out * t.out)))⁻¹ * (j s.out * t.out) = (j (q t.out))⁻¹ * t.out`. Rewrite using `[e0, map_mul, mul_inv_rev]`. Use `group`. Rewrite using `[hh, e1, e0, hfN _ hn, (hK _ (K.inv_mem (hjN _ hn)) _).1]`.

Establish `hinj : Set.InjOn φ (S₁ ×ˢ S₂ : Finset _)`. Introduce and unpack `⟨s, t⟩ hp ⟨s', t'⟩ hp' e`. Establish `ht : t ∈ S₂` using `(Finset.mem_product.1 (Finset.mem_coe.1 hp)).2`. Establish `ht' : t' ∈ S₂` using `(Finset.mem_product.1 (Finset.mem_coe.1 hp')).2`. Establish `hn : q t.out ∈ N` using `hh₁N _ ((m₂ t).1 ht)`.

Establish `hn' : q t'.out ∈ N` using `hh₁N _ ((m₂ t').1 ht')`. Establish `hk : (j s.out * t.out)⁻¹ * (j s'.out * t'.out) ∈ K` using `QuotientGroup.eq.1 e`. Establish `hq : (q t.out)⁻¹ * (s.out⁻¹ * s'.out) * q t'.out ∈ N`. Use `hqK _ hk` as an intermediate fact. Simplify `this` using `[hqj, mul_assoc]`.

Establish `hs : s.out⁻¹ * s'.out ∈ N`. Use `N.mul_mem (N.mul_mem hn hq) (N.inv_mem hn')` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `es : s = s'`. Rewrite using `[← QuotientGroup.out_eq' s, ← QuotientGroup.out_eq' s']`.

Conclude with `QuotientGroup.eq.2 hs`. Substitute `es` using the available equality. Establish `ht2 : t.out⁻¹ * t'.out ∈ K`. Simplify `hk` using `[mul_assoc]`. Establish `et : t = t'`.

Rewrite using `[← QuotientGroup.out_eq' t, ← QuotientGroup.out_eq' t']`. Conclude with `QuotientGroup.eq.2 ht2`. Rewrite using `[et]`. Establish `hsupp : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ (S₁ ×ˢ S₂).image φ`. Introduce `c hc`.

Use `set g := c.out with hg`. Use `set a := q g with ha`. Use `set x := (j a)⁻¹ * g with hx`. Rewrite `hc` using `[hh g]`. Establish `hfa : f a ≠ 0` using `left_ne_zero_of_mul hc`.

Establish `hhx : h₁ x ≠ 0` using `right_ne_zero_of_mul hc`. Take `⟨n, hn⟩` from `QuotientGroup.mk_out_eq_mul N a`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K x`. Use `Finset.mem_image.2 ⟨((a : A ⧸ N), (x : G ⧸ K)), Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ((a : A ⧸ N)) ∈ S₁`.

Rewrite using `[m₁, hn, hfN _ n.2]`. Conclude with `hfa`. Use `show ((x : G ⧸ K)) ∈ S₂`. Rewrite using `[m₂, hk, (hK _ k.2 _).2]`. Conclude with `hhx`.

Use `show ((j (a : A ⧸ N).out * (x : G ⧸ K).out : G) : G ⧸ K) = c`. Establish `c1 : Commute (j (n : A)) x` using `hcomm _ _ (hx0 g)`. Establish `e : j (a : A ⧸ N).out * (x : G ⧸ K).out = g * (j (n : A) * (k : G))`. Establish `hgx : j a * x = g` using `by rw [hx]; group`. Rewrite using `[hn, hk, map_mul, mul_assoc (j a), ← mul_assoc (j (n : A)), c1.eq, mul_assoc x, ← mul_assoc (j a), hgx]`.

Rewrite using `[e, QuotientGroup.mk_mul_of_mem _ (K.mul_mem (hjN _ n.2) k.2), hg, QuotientGroup.out_eq']`. Establish `hout : ∀ p ∈ S₁ ×ˢ S₂, h (φ p).out • ρ (φ p).out y = (f p.1.out * h₁ p.2.out) • ρ (j p.1.out * p.2.out) y`. Introduce and unpack `⟨s, t⟩ hp`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (j s.out * t.out)`. Establish `ht : t ∈ S₂` using `(Finset.mem_product.1 hp).2`.

Use `show h (((j s.out * t.out : G) : G ⧸ K)).out • ρ (((j s.out * t.out : G) : G ⧸ K)).out y = _`. Rewrite using `[hk, hright _ _ k.2, hterm s t ht, map_mul ρ (j s.out * t.out), Module.End.mul_apply, hyk _ k.2]`. Rewrite using `[lv_eq_sum ρ K h _ hsupp, lv_eq_sum (ρ.comp j) N f S₁ (fun s hs => (m₁ s).2 hs), lv_eq_sum ρ K h₁ S₂ (fun t ht => (m₂ t).2 ht)]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply]`. Rewrite using `[Finset.sum_image hinj, Finset.sum_congr rfl hout, Finset.sum_product]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, map_sum, map_smul, Finset.smul_sum, smul_smul, map_mul, Module.End.mul_apply]`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absStep_pf :
    AbsStep := by
  intro G A V _ _ _ _ ρ K N j q f h h₁ hqj hcomm hjN hqK hh hh₁N hK hfN hfs hh₁s y hy
  classical
  have hyk : ∀ k ∈ K, ρ k y = y := fun k hk => by
    have := hy ⟨k, hk⟩
    simpa using this

  have hx0 : ∀ g, q ((j (q g))⁻¹ * g) = 1 := fun g => by simp [hqj]
  have hright : ∀ g k, k ∈ K → h (g * k) = h g := by
    intro g k hk
    rw [hh (g * k), hh g]
    have e1 : f (q (g * k)) = f (q g) := by
      rw [map_mul]
      exact hfN _ (hqK k hk) _
    have c : Commute (j (q k)) ((j (q g))⁻¹ * g) := hcomm (q k) _ (hx0 g)
    have e2 : (j (q (g * k)))⁻¹ * (g * k) = ((j (q g))⁻¹ * g) * ((j (q k))⁻¹ * k) := by
      have c' : (j (q k))⁻¹ * ((j (q g))⁻¹ * g) = ((j (q g))⁻¹ * g) * (j (q k))⁻¹ := c.inv_left.eq
      rw [map_mul, map_mul, mul_inv_rev, ← mul_assoc ((j (q g))⁻¹ * g), ← c']
      simp only [mul_assoc]
    rw [e1, e2, (hK _ (K.mul_mem (K.inv_mem (hjN _ (hqK k hk))) hk) _).2]
  set S₁ : Finset (A ⧸ N) := hfs.toFinset with hS₁
  set S₂ : Finset (G ⧸ K) := hh₁s.toFinset with hS₂
  have m₁ : ∀ s, s ∈ S₁ ↔ f s.out ≠ 0 := fun s => by simp [hS₁]
  have m₂ : ∀ t, t ∈ S₂ ↔ h₁ t.out ≠ 0 := fun t => by simp [hS₂]
  let φ : (A ⧸ N) × (G ⧸ K) → G ⧸ K := fun p => ((j p.1.out * p.2.out : G) : G ⧸ K)
  have hterm : ∀ (s : A ⧸ N) (t : G ⧸ K), t ∈ S₂ → h (j s.out * t.out) = f s.out * h₁ t.out := by
    intro s t ht
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have e0 : q (j s.out * t.out) = s.out * q t.out := by rw [map_mul, hqj]
    have e1 : (j (q (j s.out * t.out)))⁻¹ * (j s.out * t.out) = (j (q t.out))⁻¹ * t.out := by
      rw [e0, map_mul, mul_inv_rev]
      group
    rw [hh, e1, e0, hfN _ hn, (hK _ (K.inv_mem (hjN _ hn)) _).1]
  have hinj : Set.InjOn φ (S₁ ×ˢ S₂ : Finset _) := by
    rintro ⟨s, t⟩ hp ⟨s', t'⟩ hp' e
    have ht : t ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp)).2
    have ht' : t' ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp')).2
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have hn' : q t'.out ∈ N := hh₁N _ ((m₂ t').1 ht')
    have hk : (j s.out * t.out)⁻¹ * (j s'.out * t'.out) ∈ K := QuotientGroup.eq.1 e
    have hq : (q t.out)⁻¹ * (s.out⁻¹ * s'.out) * q t'.out ∈ N := by
      have := hqK _ hk
      simpa [hqj, mul_assoc] using this
    have hs : s.out⁻¹ * s'.out ∈ N := by
      have := N.mul_mem (N.mul_mem hn hq) (N.inv_mem hn')
      simpa [mul_assoc] using this
    have es : s = s' := by
      rw [← QuotientGroup.out_eq' s, ← QuotientGroup.out_eq' s']
      exact QuotientGroup.eq.2 hs
    subst es
    have ht2 : t.out⁻¹ * t'.out ∈ K := by
      simpa [mul_assoc] using hk
    have et : t = t' := by
      rw [← QuotientGroup.out_eq' t, ← QuotientGroup.out_eq' t']
      exact QuotientGroup.eq.2 ht2
    rw [et]
  have hsupp : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ (S₁ ×ˢ S₂).image φ := by
    intro c hc
    set g := c.out with hg
    set a := q g with ha
    set x := (j a)⁻¹ * g with hx
    rw [hh g] at hc
    have hfa : f a ≠ 0 := left_ne_zero_of_mul hc
    have hhx : h₁ x ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    refine Finset.mem_image.2 ⟨((a : A ⧸ N), (x : G ⧸ K)), Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩
    · show ((a : A ⧸ N)) ∈ S₁
      rw [m₁, hn, hfN _ n.2]
      exact hfa
    · show ((x : G ⧸ K)) ∈ S₂
      rw [m₂, hk, (hK _ k.2 _).2]
      exact hhx
    · show ((j (a : A ⧸ N).out * (x : G ⧸ K).out : G) : G ⧸ K) = c
      have c1 : Commute (j (n : A)) x := hcomm _ _ (hx0 g)
      have e : j (a : A ⧸ N).out * (x : G ⧸ K).out = g * (j (n : A) * (k : G)) := by
        have hgx : j a * x = g := by rw [hx]; group
        rw [hn, hk, map_mul, mul_assoc (j a), ← mul_assoc (j (n : A)), c1.eq, mul_assoc x, ← mul_assoc (j a), hgx]
      rw [e, QuotientGroup.mk_mul_of_mem _ (K.mul_mem (hjN _ n.2) k.2), hg, QuotientGroup.out_eq']
  have hout : ∀ p ∈ S₁ ×ˢ S₂, h (φ p).out • ρ (φ p).out y = (f p.1.out * h₁ p.2.out) • ρ (j p.1.out * p.2.out) y := by
    rintro ⟨s, t⟩ hp
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (j s.out * t.out)
    have ht : t ∈ S₂ := (Finset.mem_product.1 hp).2
    show h (((j s.out * t.out : G) : G ⧸ K)).out • ρ (((j s.out * t.out : G) : G ⧸ K)).out y = _
    rw [hk, hright _ _ k.2, hterm s t ht, map_mul ρ (j s.out * t.out), Module.End.mul_apply, hyk _ k.2]
  rw [lv_eq_sum ρ K h _ hsupp, lv_eq_sum (ρ.comp j) N f S₁ (fun s hs => (m₁ s).2 hs),
    lv_eq_sum ρ K h₁ S₂ (fun t ht => (m₂ t).2 ht)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_image hinj, Finset.sum_congr rfl hout, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [MonoidHom.comp_apply, map_sum, map_smul, Finset.smul_sum, smul_smul, map_mul, Module.End.mul_apply]
