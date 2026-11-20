import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit

open NumberField

namespace UpperTheory.Gal.FiniteEtaleModels.O

/- English proof (translation)
Take `⟨m, hm⟩` from `hr`. Take `⟨s, t, hst⟩` from `hd`. Establish `hmA : (r : A) ^ 2 - (tr : A) * r + nm = (q : A) * m`. Use `congrArg (fun z : ℤ => (z : A)) hm` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `hstA : (s : A) * q + t * ((tr : A) ^ 2 - 4 * nm) = 1`. Use `congrArg (fun z : ℤ => (z : A)) hst` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Take `⟨v, hv⟩ : ∃ v : Ideal A, v = Ideal.span {(q : A), bar ω - (r : A)}` from `⟨_, rfl⟩`. Establish `hbb : bar (bar ω) = ω`. Use `congrArg bar h1` as an intermediate fact. Rewrite `this` using `[map_add, map_intCast]`. Take the linear combination `this - h1`.

Establish `Mu : Ideal.map bar u = v`. Rewrite using `[hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast]`. Establish `Mv : Ideal.map bar v = u`. Rewrite using `[hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast, hbb]`. Establish `pu : ∀ e, ∀ x ∈ u ^ e, bar x ∈ v ^ e` using `fun e x hx => by`.

Rewrite using `[← Mu, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem bar hx`. Establish `pv : ∀ e, ∀ x ∈ v ^ e, bar x ∈ u ^ e` using `fun e x hx => by`. Rewrite using `[← Mv, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem bar hx`.

Establish `hqu : (q : A) ∈ u` using `hu ▸ Ideal.subset_span (by simp)`. Establish `hwu : ω - (r : A) ∈ u` using `hu ▸ Ideal.subset_span (by simp)`. Establish `hwv : bar ω - (r : A) ∈ v` using `hv ▸ Ideal.subset_span (by simp)`. Establish `hsup : u ⊔ v = ⊤`. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `hd' : (tr : A) - 2 * r ∈ u ⊔ v`. Use `Ideal.add_mem _ (Ideal.mem_sup_left hwu) (Ideal.mem_sup_right hwv)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Take the linear combination `-h1`. Establish `key : (1 : A) = (q : A) * ((s : A) - 4 * t * m) + (t : A) * ((tr : A) - 2 * r) * ((tr : A) - 2 * r)`.

Take the linear combination `-hstA - 4 * (t : A) * hmA`. Rewrite using `[key]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_sup_left hqu)) (Ideal.mul_mem_left _ _ hd')`. Establish `hmul : u * v ≤ Ideal.span {(q : A)}`. Rewrite using `[hu, hv, Submodule.mul_le]`.

Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[Ideal.mem_span_pair]`. Take `⟨c, d, rfl⟩` from `hx`. Take `⟨c', d', rfl⟩` from `hy`. Rewrite using `[Ideal.mem_span_singleton']`.

Use `⟨c * c' * q + c * d' * (bar ω - r) + d * c' * (ω - r) + d * d' * m, ?_⟩` and prove the remaining obligations. Take the linear combination `(-(d * d')) * (h2 - (r : A) * h1 + hmA)`. Establish `hcop : ∀ f e, u ^ f ⊔ v ^ e = ⊤` using `fun f e => Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.pow (Ideal.isCoprime_iff_sup_eq.2 hsup))`. Establish `hinf : ∀ e, u ^ e ⊓ v ^ e ≤ Ideal.span {(q : A) ^ e}` using `fun e => by`. Rewrite using `[Ideal.inf_eq_mul_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 (hcop e e)), ← mul_pow, ← Ideal.span_singleton_pow]`.

Conclude with `Ideal.pow_right_mono hmul e`. Establish `dv : ∀ e y, y ∈ u ^ e → y ∈ v ^ e → (q : A) ^ e ∣ y` using `fun e y hy1 hy2 => Ideal.mem_span_singleton.1 (hinf e (Submodule.mem_inf.2 ⟨hy1, hy2⟩))`. Establish `ex : ∀ e, ∃ b, b ∈ v ^ e ∧ 1 - b ∈ u ^ e` using `fun e => by`. Establish `h1' : (1 : A) ∈ u ^ e ⊔ v ^ e` using `by rw [hcop e e]; exact Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 h1'`.

Conclude with `⟨b, hb, by rw [← hab, add_sub_cancel_right]; exact ha⟩`. Use `choose ε hεv hεu using ex`. Use `⟨ε, fun e => ⟨hεu e, pv e _ (hεv e), ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `dv e _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ (hεv e))`.

Apply `dv e` to reduce the goal to its premises. Establish `h3` using `Ideal.sub_mem _ (pv e _ (hεv e)) (hεu e)`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `Ideal.sub_mem _ (hεv e) (pu e _ (hεu e))`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree. Apply `dv e` to reduce the goal to its premises. Establish `h3` using `Ideal.sub_mem _ (hεu e) (Ideal.pow_le_pow_right (Nat.le_succ e) (hεu (e + 1)))`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `Ideal.sub_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) (hεv (e + 1))) (hεv e)`. Introduce and unpack `𝔞 ⟨f, hf⟩ hq x hx`. Establish `h1' : (1 : A) ∈ u ^ f ⊔ v ^ e` using `by rw [hcop f e]; exact Submodule.mem_top`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 h1'`. Establish `hx' : x = x * a + x * b` using `by rw [← mul_add, hab, mul_one]`. Rewrite using `[hx']`. Use `Ideal.add_mem _ (hf (Ideal.mul_mem_left _ _ ha)) ?_` and prove the remaining obligations. Establish `h4` using `dv e _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hb)`.

Take `⟨c, hc⟩` from `h4`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right _ _ hq`.
-/
private theorem idem_core {A : Type} [CommRing A] (bar : A ≃+* A) (ω : A) (tr nm r : ℤ) (q : ℕ)
    (h1 : ω + bar ω = (tr : A)) (h2 : ω * bar ω = (nm : A))
    (hd : IsCoprime (q : ℤ) (tr ^ 2 - 4 * nm)) (hr : (q : ℤ) ∣ r ^ 2 - tr * r + nm)
    (u : Ideal A) (hu : u = Ideal.span {(q : A), ω - (r : A)}) :
    ∃ ε : ℕ → A, ∀ e : ℕ,
      1 - ε e ∈ u ^ e ∧ bar (ε e) ∈ u ^ e ∧ (∀ x ∈ u ^ e, (q : A) ^ e ∣ ε e * x) ∧
      (q : A) ^ e ∣ ε e + bar (ε e) - 1 ∧ (q : A) ^ e ∣ ε (e + 1) - ε e ∧
      ∀ (𝔞 : Ideal A), (∃ f : ℕ, u ^ f ≤ 𝔞) → (q : A) ^ e ∈ 𝔞 → u ^ e ≤ 𝔞 := by
  classical
  obtain ⟨m, hm⟩ := hr
  obtain ⟨s, t, hst⟩ := hd
  have hmA : (r : A) ^ 2 - (tr : A) * r + nm = (q : A) * m := by
    have := congrArg (fun z : ℤ => (z : A)) hm
    push_cast at this
    exact this
  have hstA : (s : A) * q + t * ((tr : A) ^ 2 - 4 * nm) = 1 := by
    have := congrArg (fun z : ℤ => (z : A)) hst
    push_cast at this
    exact this
  obtain ⟨v, hv⟩ : ∃ v : Ideal A, v = Ideal.span {(q : A), bar ω - (r : A)} := ⟨_, rfl⟩
  have hbb : bar (bar ω) = ω := by
    have := congrArg bar h1
    rw [map_add, map_intCast] at this
    linear_combination this - h1
  have Mu : Ideal.map bar u = v := by
    rw [hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast]
  have Mv : Ideal.map bar v = u := by
    rw [hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast, hbb]
  have pu : ∀ e, ∀ x ∈ u ^ e, bar x ∈ v ^ e := fun e x hx => by
    rw [← Mu, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem bar hx
  have pv : ∀ e, ∀ x ∈ v ^ e, bar x ∈ u ^ e := fun e x hx => by
    rw [← Mv, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem bar hx
  have hqu : (q : A) ∈ u := hu ▸ Ideal.subset_span (by simp)
  have hwu : ω - (r : A) ∈ u := hu ▸ Ideal.subset_span (by simp)
  have hwv : bar ω - (r : A) ∈ v := hv ▸ Ideal.subset_span (by simp)
  have hsup : u ⊔ v = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hd' : (tr : A) - 2 * r ∈ u ⊔ v := by
      have := Ideal.add_mem _ (Ideal.mem_sup_left hwu) (Ideal.mem_sup_right hwv)
      convert this using 1
      linear_combination -h1
    have key : (1 : A) = (q : A) * ((s : A) - 4 * t * m) + (t : A) * ((tr : A) - 2 * r) * ((tr : A) - 2 * r) := by
      linear_combination -hstA - 4 * (t : A) * hmA
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_sup_left hqu)) (Ideal.mul_mem_left _ _ hd')
  have hmul : u * v ≤ Ideal.span {(q : A)} := by
    rw [hu, hv, Submodule.mul_le]
    intro x hx y hy
    rw [Ideal.mem_span_pair] at hx hy
    obtain ⟨c, d, rfl⟩ := hx
    obtain ⟨c', d', rfl⟩ := hy
    rw [Ideal.mem_span_singleton']
    refine ⟨c * c' * q + c * d' * (bar ω - r) + d * c' * (ω - r) + d * d' * m, ?_⟩
    linear_combination (-(d * d')) * (h2 - (r : A) * h1 + hmA)
  have hcop : ∀ f e, u ^ f ⊔ v ^ e = ⊤ := fun f e =>
    Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.pow (Ideal.isCoprime_iff_sup_eq.2 hsup))
  have hinf : ∀ e, u ^ e ⊓ v ^ e ≤ Ideal.span {(q : A) ^ e} := fun e => by
    rw [Ideal.inf_eq_mul_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 (hcop e e)), ← mul_pow,
      ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hmul e
  have dv : ∀ e y, y ∈ u ^ e → y ∈ v ^ e → (q : A) ^ e ∣ y := fun e y hy1 hy2 =>
    Ideal.mem_span_singleton.1 (hinf e (Submodule.mem_inf.2 ⟨hy1, hy2⟩))
  have ex : ∀ e, ∃ b, b ∈ v ^ e ∧ 1 - b ∈ u ^ e := fun e => by
    have h1' : (1 : A) ∈ u ^ e ⊔ v ^ e := by rw [hcop e e]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
    exact ⟨b, hb, by rw [← hab, add_sub_cancel_right]; exact ha⟩
  choose ε hεv hεu using ex
  refine ⟨ε, fun e => ⟨hεu e, pv e _ (hεv e), ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    exact dv e _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ (hεv e))
  · apply dv e
    · have h3 := Ideal.sub_mem _ (pv e _ (hεv e)) (hεu e)
      convert h3 using 1
      ring
    · have h3 := Ideal.sub_mem _ (hεv e) (pu e _ (hεu e))
      convert h3 using 1
      rw [map_sub, map_one]
      ring
  · apply dv e
    · have h3 := Ideal.sub_mem _ (hεu e) (Ideal.pow_le_pow_right (Nat.le_succ e) (hεu (e + 1)))
      convert h3 using 1
      ring
    · exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) (hεv (e + 1))) (hεv e)
  · rintro 𝔞 ⟨f, hf⟩ hq x hx
    have h1' : (1 : A) ∈ u ^ f ⊔ v ^ e := by rw [hcop f e]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
    have hx' : x = x * a + x * b := by rw [← mul_add, hab, mul_one]
    rw [hx']
    refine Ideal.add_mem _ (hf (Ideal.mul_mem_left _ _ ha)) ?_
    have h4 := dv e _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hb)
    obtain ⟨c, hc⟩ := h4
    rw [hc]
    exact Ideal.mul_mem_right _ _ hq

end UpperTheory.Gal.FiniteEtaleModels.O

/- English proof (translation)
Introduce `q hq D r hr`. Establish `hprime : Prime (q : ℤ)` using `Nat.prime_iff_prime_int.1 hq.out`. Conclude with `UpperTheory.Gal.FiniteEtaleModels.O.idem_core D.bar D.ω D.tr D.nm r q D.tr_eq D.nm_eq (hprime.coprime_iff_not_dvd.2 D.disc_p) hr _ rfl`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.O.idem :
    UpperTheory.Gal.FiniteEtaleModels.O.Idem := by
  intro q hq D r hr
  have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq.out
  exact UpperTheory.Gal.FiniteEtaleModels.O.idem_core D.bar D.ω D.tr D.nm r q D.tr_eq D.nm_eq
    (hprime.coprime_iff_not_dvd.2 D.disc_p) hr _ rfl
