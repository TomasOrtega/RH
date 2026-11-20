import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim

namespace ReciprocityTheory.CA

open IsLocalRing

/- English proof (translation)
Break down `eq_or_ne (Order.height b) ⊤ with hb | hb` into its components or cases. Rewrite using `[hb]`. Conclude with `le_top`. Establish `hmono : StrictMono (Subtype.val : Set.Ici a → α)` using `fun _ _ h => h`. Establish `h1 : Order.height a ≠ ⊤` using `ne_top_of_le_ne_top hb (Order.height_mono hab)`.

Establish `h2 : Order.height (⟨b, hab⟩ : Set.Ici a) ≠ ⊤` using `ne_top_of_le_ne_top hb (Order.height_le_height_apply_of_strictMono _ hmono ⟨b, hab⟩)`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp h1`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.mp h2`. Take `⟨s, hsl, hsn⟩` from `Order.exists_series_of_le_height a (n := n) hn.le`. Take `⟨t, htl, htm⟩` from `Order.exists_series_of_le_height (⟨b, hab⟩ : Set.Ici a) (n := m) hm.le`.

Rewrite using `[← hn, ← hm]`. Set `t' : LTSeries α` to `t.map Subtype.val hmono`. Establish `ht'l : t'.last = b` using `by show ((t.last : Set.Ici a) : α) = b`. Rewrite using `[htl]`. Establish `ht'len : t'.length = m` using `htm`.

Establish `hhead : a ≤ t'.head` using `t.head.2`. Break down `hhead.eq_or_lt with he | hlt` into its components or cases. Establish `hc : s.last = t'.head` using `hsl.trans he`. Establish `hlen : (s.smash t' hc).length = n + m` using `by show s.length + t'.length = n + m`. Rewrite using `[hsn, ht'len]`.

Establish `hlast : (s.smash t' hc).last = b` using `by first`. Consider the case `(rw [RelSeries.last_smash]; exact ht'l)`. Consider the case `(rw [RelSeries.smash_last]; exact ht'l)`. Consider the case `simp [ht'l]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc : s.last < t'.head` using `by rw [hsl]; exact hlt`. Establish `hlen : (s.append t' hc).length = n + m + 1` using `by show s.length + t'.length + 1 = n + m + 1`. Rewrite using `[hsn, ht'len]`. Establish `hlast : (s.append t' hc).last = b` using `by first`. Consider the case `(rw [RelSeries.last_append]; exact ht'l)`.

Consider the case `(rw [RelSeries.append_last]; exact ht'l)`. Consider the case `simp [ht'l]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem height_add_height_Ici_le {α : Type*} [PartialOrder α] {a b : α} (hab : a ≤ b) :
    Order.height a + Order.height (⟨b, hab⟩ : Set.Ici a) ≤ Order.height b := by
  rcases eq_or_ne (Order.height b) ⊤ with hb | hb
  · rw [hb]; exact le_top
  have hmono : StrictMono (Subtype.val : Set.Ici a → α) := fun _ _ h => h
  have h1 : Order.height a ≠ ⊤ := ne_top_of_le_ne_top hb (Order.height_mono hab)
  have h2 : Order.height (⟨b, hab⟩ : Set.Ici a) ≠ ⊤ :=
    ne_top_of_le_ne_top hb (Order.height_le_height_apply_of_strictMono _ hmono ⟨b, hab⟩)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h1
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h2
  obtain ⟨s, hsl, hsn⟩ := Order.exists_series_of_le_height a (n := n) hn.le
  obtain ⟨t, htl, htm⟩ := Order.exists_series_of_le_height (⟨b, hab⟩ : Set.Ici a) (n := m) hm.le
  rw [← hn, ← hm]
  let t' : LTSeries α := t.map Subtype.val hmono
  have ht'l : t'.last = b := by
    show ((t.last : Set.Ici a) : α) = b
    rw [htl]
  have ht'len : t'.length = m := htm
  have hhead : a ≤ t'.head := t.head.2
  rcases hhead.eq_or_lt with he | hlt
  ·
    have hc : s.last = t'.head := hsl.trans he
    have hlen : (s.smash t' hc).length = n + m := by
      show s.length + t'.length = n + m
      rw [hsn, ht'len]
    have hlast : (s.smash t' hc).last = b := by
      first
      | (rw [RelSeries.last_smash]; exact ht'l)
      | (rw [RelSeries.smash_last]; exact ht'l)
      | simp [ht'l]
    calc ((n : ℕ∞) + (m : ℕ∞)) = ((s.smash t' hc).length : ℕ∞) := by rw [hlen]; norm_cast
      _ ≤ Order.height b := Order.length_le_height hlast.le
  ·
    have hc : s.last < t'.head := by rw [hsl]; exact hlt
    have hlen : (s.append t' hc).length = n + m + 1 := by
      show s.length + t'.length + 1 = n + m + 1
      rw [hsn, ht'len]
    have hlast : (s.append t' hc).last = b := by
      first
      | (rw [RelSeries.last_append]; exact ht'l)
      | (rw [RelSeries.append_last]; exact ht'l)
      | simp [ht'l]
    calc ((n : ℕ∞) + (m : ℕ∞)) ≤ ((n + m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ (n + m)
      _ = ((s.append t' hc).length : ℕ∞) := by rw [hlen]
      _ ≤ Order.height b := Order.length_le_height hlast.le

/- English proof (translation)
Establish `hmin : I.minimalPrimes = {I}` using `Ideal.minimalPrimes_eq_subsingleton_self`. Unfold `Ideal.height`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `iInf₂_le I (by rw [hmin]; rfl)`. Use `le_iInf₂ fun J hJ => ?_` and prove the remaining obligations.

Establish `hJI : J = I` using `by rw [hmin] at hJ; exact hJ`. Substitute `hJI` using the available equality. Conclude with `le_rfl`.
-/
private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (I : Ideal R)
    [hI : I.IsPrime] : I.height = Order.height (⟨I, hI⟩ : PrimeSpectrum R) := by
  have hmin : I.minimalPrimes = {I} := Ideal.minimalPrimes_eq_subsingleton_self
  unfold Ideal.height
  apply le_antisymm
  · exact iInf₂_le I (by rw [hmin]; rfl)
  · refine le_iInf₂ fun J hJ => ?_
    have hJI : J = I := by rw [hmin] at hJ; exact hJ
    subst hJI
    exact le_rfl

/- English proof (translation)
Use `haveI hq' : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)`. Rewrite using `[height_eq_order_height_lemma p, height_eq_order_height_lemma q, height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]`. Establish `hpq' : (⟨p, ‹_›⟩ : PrimeSpectrum P) ≤ ⟨q, ‹_›⟩` using `hpq`. Set `f : PrimeSpectrum (P ⧸ p) → Set.Ici (⟨p, ‹_›⟩ : PrimeSpectrum P)` to `fun x => ⟨⟨Ideal.comap (Ideal.Quotient.mk p) x.asIdeal, inferInstance⟩, fun z hz => by show z ∈ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]`.

Conclude with `x.asIdeal.zero_mem⟩`. Establish `hf : StrictMono f`. Introduce `x y hxy`. Use `show Ideal.comap (Ideal.Quotient.mk p) x.asIdeal < Ideal.comap (Ideal.Quotient.mk p) y.asIdeal`. Use `lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)) fun e => ?_` and prove the remaining obligations.

Conclude with `hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e))`. Establish `hfq : f ⟨q.map (Ideal.Quotient.mk p), hq'⟩ = ⟨⟨q, ‹_›⟩, hpq'⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap (Ideal.Quotient.mk p) (q.map (Ideal.Quotient.mk p)) = q`.

Use extensionality with `z`. Rewrite using `[Ideal.mem_comap]`. Use `first`. Consider the case `exact Ideal.mem_quotient_iff_mem hpq`. Consider the case `exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr hpq])`.

Establish `hle` using `Order.height_le_height_apply_of_strictMono f hf ⟨q.map (Ideal.Quotient.mk p), hq'⟩`. Rewrite `hle` using `[hfq]`. Conclude with `(add_le_add le_rfl hle).trans (height_add_height_Ici_le hpq')`.
-/
theorem height_add_height_map_quotient_le {P : Type*} [CommRing P] (p q : Ideal P) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) : p.height + (q.map (Ideal.Quotient.mk p)).height ≤ q.height := by
  haveI hq' : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)
  rw [height_eq_order_height_lemma p, height_eq_order_height_lemma q,
    height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]
  have hpq' : (⟨p, ‹_›⟩ : PrimeSpectrum P) ≤ ⟨q, ‹_›⟩ := hpq

  let f : PrimeSpectrum (P ⧸ p) → Set.Ici (⟨p, ‹_›⟩ : PrimeSpectrum P) := fun x =>
    ⟨⟨Ideal.comap (Ideal.Quotient.mk p) x.asIdeal, inferInstance⟩, fun z hz => by
      show z ∈ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact x.asIdeal.zero_mem⟩
  have hf : StrictMono f := by
    intro x y hxy
    show Ideal.comap (Ideal.Quotient.mk p) x.asIdeal < Ideal.comap (Ideal.Quotient.mk p) y.asIdeal
    refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)) fun e => ?_
    exact hxy.ne (PrimeSpectrum.ext
      (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e))
  have hfq : f ⟨q.map (Ideal.Quotient.mk p), hq'⟩ = ⟨⟨q, ‹_›⟩, hpq'⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk p) (q.map (Ideal.Quotient.mk p)) = q
    ext z
    rw [Ideal.mem_comap]
    first
    | exact Ideal.mem_quotient_iff_mem hpq
    | exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr hpq])
  have hle := Order.height_le_height_apply_of_strictMono f hf ⟨q.map (Ideal.Quotient.mk p), hq'⟩
  rw [hfq] at hle
  exact (add_le_add le_rfl hle).trans (height_add_height_Ici_le hpq')

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[Ideal.mem_comap]`. Use `first`. Consider the case `exact Ideal.mem_quotient_iff_mem h`. Consider the case `exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr h])`.
-/
private theorem comap_map_mk_lemma_4 {R : Type*} [CommRing R] (I J : Ideal R) (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (J.map (Ideal.Quotient.mk I)) = J := by
  ext z
  rw [Ideal.mem_comap]
  first
  | exact Ideal.mem_quotient_iff_mem h
  | exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr h])

/- English proof (translation)
Establish `hmono : ∀ s : LTSeries α, Monotone s` using `fun s => by first`. Consider the case `exact s.monotone`. Consider the case `exact s.strictMono.monotone`. Establish `H : ∀ s : LTSeries α, s.last ≤ a → (s.length : ℕ∞) ≤ Order.height (f ⟨a, le_rfl⟩)`. Introduce `s hs`.

Set `t : LTSeries β` to `{ length := s.length toFun := fun i => f ⟨s i, (hmono s (Fin.le_last i)).trans hs⟩ step := fun i => hf (Subtype.mk_lt_mk.mpr (s.step i)) }`. Establish `ht : t.last ≤ f ⟨a, le_rfl⟩` using `by show f ⟨s (Fin.last s.length), _⟩ ≤ f ⟨a, le_rfl⟩`. Conclude with `hf.monotone (show s (Fin.last s.length) ≤ a from hs)`. Conclude with `Order.length_le_height ht`. Use `first`.

Consider the case `exact Order.height_le_iff.mpr fun s hs => H s hs.le`. Consider the case `exact Order.height_le fun s hs => H s hs.le`. Consider the case `(unfold Order.height; exact iSup₂_le fun s hs => H s hs)`.
-/
private theorem height_le_height_Iic_lemma_2 {α β : Type*} [PartialOrder α] [Preorder β] (a : α)
    (f : Set.Iic a → β) (hf : StrictMono f) : Order.height a ≤ Order.height (f ⟨a, le_rfl⟩) := by
  have hmono : ∀ s : LTSeries α, Monotone s := fun s => by
    first
    | exact s.monotone
    | exact s.strictMono.monotone
  have H : ∀ s : LTSeries α, s.last ≤ a → (s.length : ℕ∞) ≤ Order.height (f ⟨a, le_rfl⟩) := by
    intro s hs
    let t : LTSeries β :=
      { length := s.length
        toFun := fun i => f ⟨s i, (hmono s (Fin.le_last i)).trans hs⟩
        step := fun i => hf (Subtype.mk_lt_mk.mpr (s.step i)) }
    have ht : t.last ≤ f ⟨a, le_rfl⟩ := by
      show f ⟨s (Fin.last s.length), _⟩ ≤ f ⟨a, le_rfl⟩
      exact hf.monotone (show s (Fin.last s.length) ≤ a from hs)
    exact Order.length_le_height ht
  first
  | exact Order.height_le_iff.mpr fun s hs => H s hs.le
  | exact Order.height_le fun s hs => H s hs.le
  | (unfold Order.height; exact iSup₂_le fun s hs => H s hs)

/- English proof (translation)
Unfold `Order.krullDim`. Use `iSup_le fun s => ?_` and prove the remaining obligations. Establish `h` using `Order.length_le_height (p := s.map f hf) (x := b) (hb s.last)`. Conclude with `h` after adjusting the coercions.
-/
private theorem krullDim_le_height_lemma_3 {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : StrictMono f) (b : β) (hb : ∀ x, f x ≤ b) :
    Order.krullDim α ≤ (Order.height b : WithBot ℕ∞) := by
  unfold Order.krullDim
  refine iSup_le fun s => ?_
  have h := Order.length_le_height (p := s.map f hf) (x := b) (hb s.last)
  exact_mod_cast h

/- English proof (translation)
Use `first`. Consider the case `exact Order.height_le_krullDim a`. Consider the case `(have H : ∀ s : LTSeries α, ((s.length : ℕ∞) : WithBot ℕ∞) ≤ Order.krullDim α := fun s => by`. Use `le_iSup (fun s : LTSeries α => (s.length : WithBot ℕ∞)) s` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Take `⟨k, hk⟩` from `WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.coe_ne_bot (H (RelSeries.singleton _ a)))`. Rewrite using `[← hk]`. Use `WithBot.coe_le_coe.mpr (Order.height_le_iff.mpr fun s _ => ?_)` and prove the remaining obligations. Conclude with `WithBot.coe_le_coe.mp (by rw [hk]; exact H s))`.
-/
private theorem height_le_krullDim_lemma_6 {α : Type*} [Preorder α] (a : α) :
    (Order.height a : WithBot ℕ∞) ≤ Order.krullDim α := by
  first
  | exact Order.height_le_krullDim a
  | (have H : ∀ s : LTSeries α, ((s.length : ℕ∞) : WithBot ℕ∞) ≤ Order.krullDim α := fun s => by
       have := le_iSup (fun s : LTSeries α => (s.length : WithBot ℕ∞)) s
       exact_mod_cast this
     obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp
       (ne_bot_of_le_ne_bot WithBot.coe_ne_bot (H (RelSeries.singleton _ a)))
     rw [← hk]
     refine WithBot.coe_le_coe.mpr (Order.height_le_iff.mpr fun s _ => ?_)
     exact WithBot.coe_le_coe.mp (by rw [hk]; exact H s))

/- English proof (translation)
Use `haveI hQ : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)`. Establish `hdisj : Disjoint (q.primeCompl : Set P) (p : Set P)` using `Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)`. Use `haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj`. Rewrite using `[height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]`. Use `show Order.krullDim (PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))) = _`.

Establish `hpA : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))), p ≤ Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)`. Introduce `x z hz`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hz)]`. Conclude with `x.asIdeal.zero_mem`. Establish `hAq : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))), Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal) ≤ q`.

Introduce `x z hz`. Assume the negation of the conclusion as `hzq`. Rewrite `hz` using `[Ideal.mem_comap, Ideal.mem_comap]`. Conclude with `x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz ((IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))))`. Apply `le_antisymm` to reduce the goal to its premises.

Use `krullDim_le_height_lemma_3 (fun x => (⟨(Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map (Ideal.Quotient.mk p), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw …` and prove the remaining obligations. Introduce `x y hxy show (Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map (Ideal.Quotient.mk p) < (Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map ( …`. Use `lt_of_le_of_ne (Ideal.map_mono (Ideal.comap_mono (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)))) fun e => hxy.ne ?_` and prove the remaining obligations. Establish `e1` using `congrArg (Ideal.comap (Ideal.Quotient.mk p)) e`. Rewrite `e1` using `[comap_map_mk_lemma_4 _ _ (hpA x), comap_map_mk_lemma_4 _ _ (hpA y)]`.

Establish `e2` using `congrArg (Ideal.map (algebraMap P (Localization.AtPrime q))) e1`. Rewrite `e2` using `[IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q), IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)]`. Conclude with `PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2)`. Introduce `x show _ ≤ q.map (Ideal.Quotient.mk p)`. Conclude with `Ideal.map_mono (hAq x)`.

Establish `hpB : ∀ x : PrimeSpectrum (P ⧸ p), p ≤ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal`. Introduce `x z hz`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]`. Conclude with `x.asIdeal.zero_mem`. Establish `hB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal ≤ q` using `fun x => (Ideal.comap_mono (show x.1.asIdeal ≤ q.map (Ideal.Quotient.mk p) from x.2)).trans (comap_map_mk_lemma_4 p q hpq).le`.

Establish `hdB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Disjoint (q.primeCompl : Set P) (Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal : Set P)` using `fun x => Set.disjoint_left.mpr fun z hz hzB => hz (hB x hzB)`. Establish `hBprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).IsPrime` using `fun x => IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance (hdB x)`. Establish `hCprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), (((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))).IsPrime`. Introduce `x`. Use `haveI := hBprime x`.

Conclude with `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact Ideal.map_mono (hpB x.1))`. Set `h : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)) → PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))` to `fun x => ⟨_, hCprime x⟩`. Establish `hh : StrictMono h`. Introduce `x y hxy`. Use `show ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) < ((Ideal.comap (Ideal.Quotient.mk p) y.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).map (Ideal.Qu …`.

Use `lt_of_le_of_ne (Ideal.map_mono (Ideal.map_mono (Ideal.comap_mono (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le)))) fun e => hxy.ne ?_` and prove the remaining obligations. Establish `e1` using `congrArg (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))) e`. Rewrite `e1` using `[comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB x.1)), comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB y.1))]`. Establish `e2` using `congrArg (Ideal.under P) e1`. Rewrite `e2` using `[IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q) inferInstance (hdB x), IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q) inferInstance (hdB y)]`.

Conclude with `Subtype.ext (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ringKrullDim_localization_quotient_eq_height {P : Type*} [CommRing P] (p q : Ideal P)
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) =
      ((q.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by
  haveI hQ : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  rw [height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]
  show Order.krullDim (PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))) = _

  have hpA : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))),
      p ≤ Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal) := by
    intro x z hz
    rw [Ideal.mem_comap, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hz)]
    exact x.asIdeal.zero_mem
  have hAq : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))),
      Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal) ≤ q := by
    intro x z hz
    by_contra hzq
    rw [Ideal.mem_comap, Ideal.mem_comap] at hz
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz
      ((IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))))
  apply le_antisymm
  · refine krullDim_le_height_lemma_3 (fun x => (⟨(Ideal.comap (algebraMap P (Localization.AtPrime q))
        (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map (Ideal.Quotient.mk p),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
          (by rw [Ideal.mk_ker]; exact hpA x)⟩ : PrimeSpectrum (P ⧸ p))) ?_ _ ?_
    · intro x y hxy
      show (Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map
          (Ideal.Quotient.mk p) < (Ideal.comap (algebraMap P (Localization.AtPrime q))
          (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) y.asIdeal)).map (Ideal.Quotient.mk p)
      refine lt_of_le_of_ne (Ideal.map_mono (Ideal.comap_mono (Ideal.comap_mono
        (show x.asIdeal ≤ y.asIdeal from hxy.le)))) fun e => hxy.ne ?_
      have e1 := congrArg (Ideal.comap (Ideal.Quotient.mk p)) e
      rw [comap_map_mk_lemma_4 _ _ (hpA x), comap_map_mk_lemma_4 _ _ (hpA y)] at e1
      have e2 := congrArg (Ideal.map (algebraMap P (Localization.AtPrime q))) e1
      rw [IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2)
    · intro x
      show _ ≤ q.map (Ideal.Quotient.mk p)
      exact Ideal.map_mono (hAq x)
  · have hpB : ∀ x : PrimeSpectrum (P ⧸ p), p ≤ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal := by
      intro x z hz
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact x.asIdeal.zero_mem
    have hB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal ≤ q := fun x =>
      (Ideal.comap_mono (show x.1.asIdeal ≤ q.map (Ideal.Quotient.mk p) from x.2)).trans
        (comap_map_mk_lemma_4 p q hpq).le
    have hdB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Disjoint (q.primeCompl : Set P)
        (Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal : Set P) := fun x =>
      Set.disjoint_left.mpr fun z hz hzB => hz (hB x hzB)
    have hBprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)),
        ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).IsPrime :=
      fun x => IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance (hdB x)
    have hCprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), (((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map
        (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))).IsPrime := by
      intro x
      haveI := hBprime x
      exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact Ideal.map_mono (hpB x.1))
    let h : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)) → PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) := fun x => ⟨_, hCprime x⟩
    have hh : StrictMono h := by
      intro x y hxy
      show ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).map
          (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) < ((Ideal.comap (Ideal.Quotient.mk p) y.1.asIdeal).map
          (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))
      refine lt_of_le_of_ne (Ideal.map_mono (Ideal.map_mono (Ideal.comap_mono
        (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le)))) fun e => hxy.ne ?_
      have e1 := congrArg (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))) e
      rw [comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB x.1)),
        comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB y.1))] at e1
      have e2 := congrArg (Ideal.under P) e1
      rw [IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q)
          inferInstance (hdB x),
        IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q)
          inferInstance (hdB y)] at e2
      exact Subtype.ext (PrimeSpectrum.ext
        (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2))
    calc ((Order.height (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)) : ℕ∞) :
          WithBot ℕ∞)
        ≤ (Order.height (h ⟨⟨q.map (Ideal.Quotient.mk p), hQ⟩, Set.mem_Iic.mpr le_rfl⟩) :
          WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr (height_le_height_Iic_lemma_2 _ h hh)
      _ ≤ Order.krullDim (PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))) := height_le_krullDim_lemma_6 _

/- English proof (translation)
Establish `hdisj : ∀ I : Ideal R, I ≤ q → Disjoint (q.primeCompl : Set R) (I : Set R)` using `fun I hI => Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)`. Rewrite using `[height_eq_order_height_lemma (p.map (algebraMap R (Localization.AtPrime q))), height_eq_order_height_lemma p]`. Apply `le_antisymm` to reduce the goal to its premises. Set `f : PrimeSpectrum (Localization.AtPrime q) → PrimeSpectrum R` to `fun x => ⟨Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal, inferInstance⟩`. Establish `hf : StrictMono f`.

Introduce `x y hxy`. Use `show Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal < Ideal.comap (algebraMap R (Localization.AtPrime q)) y.asIdeal`. Use `lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)) fun e => hxy.ne ?_` and prove the remaining obligations. Establish `e2` using `congrArg (Ideal.map (algebraMap R (Localization.AtPrime q))) e`. Rewrite `e2` using `[IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q), IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)]`.

Conclude with `PrimeSpectrum.ext e2`. Establish `hfp : f ⟨_, hp'⟩ = ⟨p, ‹p.IsPrime›⟩` using `PrimeSpectrum.ext (by show Ideal.under R (p.map (algebraMap R (Localization.AtPrime q))) = p`. Conclude with `IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q) ‹p.IsPrime› (hdisj p hpq))`. Establish `h` using `Order.height_le_height_apply_of_strictMono f hf ⟨_, hp'⟩`. Rewrite `h` using `[hfp]`. Then use the resulting hypothesis.

Set `g : Set.Iic (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) → PrimeSpectrum (Localization.AtPrime q)` to `fun x => ⟨x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)), IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq))⟩`. Establish `hg : StrictMono g`. Introduce `x y hxy`. Use `show x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) < y.1.asIdeal.map (algebraMap R (Localization.AtPrime q))`. Use `lt_of_le_of_ne (Ideal.map_mono (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le)) fun e => hxy.ne ?_` and prove the remaining obligations.

Establish `e2` using `congrArg (Ideal.under R) e`. Rewrite `e2` using `[IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q) inferInstance (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq)), IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q) inferInstance (hdisj …`. Conclude with `Subtype.ext (PrimeSpectrum.ext e2)`. Conclude with `height_le_height_Iic_lemma_2 _ g hg`.
-/
private theorem height_map_atPrime_lemma_5 {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) [hp' : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime] :
    (p.map (algebraMap R (Localization.AtPrime q))).height = p.height := by
  have hdisj : ∀ I : Ideal R, I ≤ q → Disjoint (q.primeCompl : Set R) (I : Set R) := fun I hI =>
    Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
  rw [height_eq_order_height_lemma (p.map (algebraMap R (Localization.AtPrime q))),
    height_eq_order_height_lemma p]
  apply le_antisymm
  · let f : PrimeSpectrum (Localization.AtPrime q) → PrimeSpectrum R := fun x =>
      ⟨Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal, inferInstance⟩
    have hf : StrictMono f := by
      intro x y hxy
      show Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal <
        Ideal.comap (algebraMap R (Localization.AtPrime q)) y.asIdeal
      refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.map (algebraMap R (Localization.AtPrime q))) e
      rw [IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext e2
    have hfp : f ⟨_, hp'⟩ = ⟨p, ‹p.IsPrime›⟩ := PrimeSpectrum.ext (by
      show Ideal.under R (p.map (algebraMap R (Localization.AtPrime q))) = p
      exact IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
        (S := Localization.AtPrime q) ‹p.IsPrime› (hdisj p hpq))
    have h := Order.height_le_height_apply_of_strictMono f hf ⟨_, hp'⟩
    rwa [hfp] at h
  · let g : Set.Iic (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) → PrimeSpectrum (Localization.AtPrime q) :=
      fun x => ⟨x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)),
        IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq))⟩
    have hg : StrictMono g := by
      intro x y hxy
      show x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) <
        y.1.asIdeal.map (algebraMap R (Localization.AtPrime q))
      refine lt_of_le_of_ne (Ideal.map_mono (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.under R) e
      rw [IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq)),
        IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show y.1.asIdeal ≤ p from y.2).trans hpq))] at e2
      exact Subtype.ext (PrimeSpectrum.ext e2)
    exact height_le_height_Iic_lemma_2 _ g hg

/- English proof (translation)
Establish `hL` using `h.localization_atPrime q`. Establish `hdisj : Disjoint (q.primeCompl : Set P) (p : Set P)` using `Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)`. Use `haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj`. Establish `e` using `hL.height_add_ringKrullDim_quotient (p.map (algebraMap P (Localization.AtPrime q)))`. Establish `e1 : (p.map (algebraMap P (Localization.AtPrime q))).height = p.height` using `height_map_atPrime_lemma_5 p q hpq`.

Establish `e2 : ringKrullDim (Localization.AtPrime q) = q.height` using `by first`. Consider the case `exact IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)`. Consider the case `(haveI hqL : (q.map (algebraMap P (Localization.AtPrime q))).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ q ‹_› (Set.disjoint_left.mpr fun x hx hxq => hx hxq)`. Rewrite using `[← height_map_atPrime_lemma_5 q q le_rfl, height_eq_order_height_lemma (q.map (algebraMap P (Localization.AtPrime q)))]`. Apply `le_antisymm` to reduce the goal to its premises.

Use `krullDim_le_height_lemma_3 id strictMono_id _ fun x => ?_ show x.asIdeal ≤ q.map (algebraMap P (Localization.AtPrime q))` and prove the remaining obligations. Rewrite using `[← IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q) x.asIdeal]`. Use `Ideal.map_mono fun z hz => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hzq`. Conclude with `x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hz) (IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)))`.

Conclude with `height_le_krullDim_lemma_6 _)`. Rewrite `e` using `[ringKrullDim_localization_quotient_eq_height p q hpq, e1, e2]`. Conclude with `e.symm` after adjusting the coercions.
-/
theorem IsCM.height_eq_height_add_height_map_quotient {P : Type*} [CommRing P] [IsLocalRing P]
    (h : IsCM P) (p q : Ideal P) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hL := h.localization_atPrime q
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have e := hL.height_add_ringKrullDim_quotient (p.map (algebraMap P (Localization.AtPrime q)))
  have e1 : (p.map (algebraMap P (Localization.AtPrime q))).height = p.height :=
    height_map_atPrime_lemma_5 p q hpq
  have e2 : ringKrullDim (Localization.AtPrime q) = q.height := by
    first
    | exact IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    | (haveI hqL : (q.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
         IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ q ‹_›
           (Set.disjoint_left.mpr fun x hx hxq => hx hxq)
       rw [← height_map_atPrime_lemma_5 q q le_rfl,
         height_eq_order_height_lemma (q.map (algebraMap P (Localization.AtPrime q)))]
       apply le_antisymm
       · refine krullDim_le_height_lemma_3 id strictMono_id _ fun x => ?_
         show x.asIdeal ≤ q.map (algebraMap P (Localization.AtPrime q))
         rw [← IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)
           x.asIdeal]
         refine Ideal.map_mono fun z hz => ?_
         by_contra hzq
         exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hz)
           (IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)))
       · exact height_le_krullDim_lemma_6 _)
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, e1, e2] at e
  exact_mod_cast e.symm

end ReciprocityTheory.CA
