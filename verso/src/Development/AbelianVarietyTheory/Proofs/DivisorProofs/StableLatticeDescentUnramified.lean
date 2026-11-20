import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

def consZero (n : ℕ) : (Fin n → R') →ₗ[R'] (Fin (n + 1) → R') where
  toFun w := Fin.cons 0 w
  map_add' w w' := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

omit [Algebra R R'] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma consZero_zero (n : ℕ) (w : Fin n → R') : consZero n w 0 = 0 := rfl

omit [Algebra R R'] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma consZero_succ (n : ℕ) (w : Fin n → R') (j : Fin n) : consZero n w j.succ = w j := rfl

/- English proof (translation)
Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => intro x _; exact ⟨0, by simp⟩`. Consider the case `succ a ih`. Introduce `x hx`.

Take `⟨c0, hc0⟩` from `hres x fun σ hσ => (dvd_pow_self _ (Nat.succ_ne_zero a)).trans (hx σ hσ)`. Take `⟨t, ht⟩` from `hc0`. Establish `hx' : x = algebraMap R R' c0 + algebraMap R R' ϖ * t` using `by rw [← ht]; ring`. Establish `ht' : ∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ t - t`. Introduce `σ hσ`.

Establish `h` using `hx σ hσ`. Establish `e : σ x - x = algebraMap R R' ϖ * (σ t - t)`. Rewrite using `[hx']`. Simplify using `only [map_add, map_mul, AlgEquiv.commutes]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e, pow_succ']`. Conclude with `(mul_dvd_mul_iff_left hπ).mp h`. Take `⟨c1, hc1⟩` from `ih t ht'`. Use `⟨c0 + ϖ * c1, ?_⟩` and prove the remaining obligations. Establish `e : x - algebraMap R R' (c0 + ϖ * c1) = algebraMap R R' ϖ * (t - algebraMap R R' c1)`.

Rewrite using `[hx']`. Simplify using `only [map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, pow_succ']`. Conclude with `mul_dvd_mul_left _ hc1`.
-/
theorem scalar_descent [IsDomain R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hπ : algebraMap R R' ϖ ≠ 0)
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) :
    ∀ (a : ℕ) (x : R'), (∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ x - x) →
      ∃ c : R, (algebraMap R R' ϖ) ^ a ∣ x - algebraMap R R' c := by
  intro a
  induction a with
  | zero => intro x _; exact ⟨0, by simp⟩
  | succ a ih =>
    intro x hx
    obtain ⟨c0, hc0⟩ := hres x fun σ hσ => (dvd_pow_self _ (Nat.succ_ne_zero a)).trans (hx σ hσ)
    obtain ⟨t, ht⟩ := hc0
    have hx' : x = algebraMap R R' c0 + algebraMap R R' ϖ * t := by rw [← ht]; ring
    have ht' : ∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ t - t := by
      intro σ hσ
      have h := hx σ hσ
      have e : σ x - x = algebraMap R R' ϖ * (σ t - t) := by
        rw [hx']; simp only [map_add, map_mul, AlgEquiv.commutes]; ring
      rw [e, pow_succ'] at h
      exact (mul_dvd_mul_iff_left hπ).mp h
    obtain ⟨c1, hc1⟩ := ih t ht'
    refine ⟨c0 + ϖ * c1, ?_⟩
    have e : x - algebraMap R R' (c0 + ϖ * c1) = algebraMap R R' ϖ * (t - algebraMap R R' c1) := by
      rw [hx']; simp only [map_add, map_mul]; ring
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hc1

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

/- English proof (translation)
Establish `hπ : algebraMap R R' ϖ ≠ 0` using `hirr.ne_zero`. Establish `hfix : ∀ (σ : R' ≃ₐ[R] R') (y : R'), y ∈ Set.range (algebraMap R R') → σ y = y`. Introduce and unpack `σ y ⟨c, rfl⟩`. Conclude with `AlgEquiv.commutes σ c`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `N _ _`. Use `⟨fun v _ => ?_, fun u _ => ⟨0, fun i => i.elim0, ?_⟩⟩` and prove the remaining obligations. Establish `: v = 0` using `Subsingleton.elim _ _`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Establish `: u - 0 = 0` using `Subsingleton.elim _ _`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `succ n ih`. Introduce `N hlat hstab`. Use `set π := algebraMap R R' ϖ with hπdef`. Set `L` to `consZero (R' := R') n`. Establish `hLact : ∀ (σ : R' ≃ₐ[R] R') (w : Fin n → R'), (fun i => σ (L w i)) = L (fun i => σ (w i))`.

Introduce `σ w`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ ?_ i <;> simp [L]`. Set `K` to `N.comap L`. Establish `hKlat : ∀ w : Fin n → R', π ^ r • w ∈ K` using `fun w => by show L (π ^ r • w) ∈ N`.

Rewrite using `[L.map_smul]`. Conclude with `hlat _`. Establish `hKstab : ∀ σ ∈ D, ∀ w ∈ K, (fun i => σ (w i)) ∈ K`. Introduce `σ hσ w hw`. Use `show L _ ∈ N`.

Rewrite using `[← hLact]`. Conclude with `hstab σ hσ _ hw`. Take `⟨hPK, hQK⟩` from `ih K hKlat hKstab`. Set `I : Ideal R'` to `N.map (LinearMap.proj (R := R') (φ := fun _ : Fin (n + 1) => R') 0)`. Establish `hrI : π ^ r ∈ I` using `⟨π ^ r • (fun _ => 1 : Fin (n + 1) → R'), hlat _, by simp⟩`.

Establish `hI0 : I ≠ ⊥`. Introduce `h`. Rewrite `hrI` using `[h, Submodule.mem_bot]`. Conclude with `pow_ne_zero r hπ hrI`. Take `⟨a, ha⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hirr`.

Establish `hmemI : ∀ v ∈ N, π ^ a ∣ v 0`. Introduce `v hv`. Establish `: v 0 ∈ I` using `⟨v, hv, rfl⟩`. Rewrite `this` using `[ha, Ideal.mem_span_singleton]`. Conclude with `this`.

Choose the witnesses or unpack the hypotheses as in `⟨vs, hvsN, hvs0⟩ : ∃ v ∈ N, v 0 = π ^ a := by`. Establish `: π ^ a ∈ I` using `by rw [ha]; exact Ideal.subset_span rfl`. Take `⟨v, hv, hv0⟩` from `this`. Conclude with `⟨v, hv, hv0⟩`. Establish `hpa : π ^ a ∈ Set.range (algebraMap R R')` using `⟨ϖ ^ a, by simp [hπdef]⟩`.

Establish `hvsK : ∀ σ ∈ D, (fun i => σ (Fin.tail vs i)) - Fin.tail vs ∈ K`. Introduce `σ hσ`. Establish `e : L ((fun i => σ (Fin.tail vs i)) - Fin.tail vs) = (fun i => σ (vs i)) - vs`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations.

Simplify using `[L, hvs0, hfix σ _ hpa]`. Introduce `j`. Simplify using `[L, Fin.tail]`. Use `show L _ ∈ N`. Rewrite using `[e]`.

Conclude with `N.sub_mem (hstab σ hσ _ hvsN) hvsN`. Take `⟨a0, ha0, ha0K⟩` from `hQK (Fin.tail vs) hvsK`. Take `⟨vo, hvo⟩ : ∃ vo, vo = vs - L (Fin.tail vs - a0)` from `⟨_, rfl⟩`. Establish `hvoN : vo ∈ N` using `hvo ▸ N.sub_mem hvsN ha0K`. Establish `hvo0 : vo 0 = π ^ a` using `by rw [hvo]; simp [L, hvs0]`.

Establish `hvorat : ∀ i, vo i ∈ Set.range (algebraMap R R')`. Introduce `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Rewrite using `[hvo0]`. Conclude with `hpa`.

Introduce `j`. Establish `: vo j.succ = a0 j` using `by rw [hvo]; simp [L, Fin.tail]`. Rewrite using `[this]`. Conclude with `ha0 j`. Establish `hrat_add : ∀ x y : R', x ∈ Set.range (algebraMap R R') → y ∈ Set.range (algebraMap R R') → x + y ∈ Set.range (algebraMap R R')`.

Introduce and unpack `_ _ ⟨c, rfl⟩ ⟨d, rfl⟩`. Conclude with `⟨c + d, map_add _ _ _⟩`. Establish `hrat0 : (0 : R') ∈ Set.range (algebraMap R R')` using `⟨0, map_zero _⟩`. Establish `hLrat : ∀ w : Fin n → R', (∀ i, w i ∈ Set.range (algebraMap R R')) → ∀ i, L w i ∈ Set.range (algebraMap R R')`. Introduce `w hw i`.

Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Simplify `hrat0` using `[L]`. Introduce `j`. Simplify `hw j` using `[L]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv`. Take `⟨t, ht⟩` from `hmemI v hv`. Take `⟨w, hw⟩ : ∃ w, w = Fin.tail (v - t • vo)` from `⟨_, rfl⟩`. Establish `hLw : L w = v - t • vo`. Use function extensionality and compare the values at `i`.

Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Simplify using `[L, ht, hvo0]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j`. Simplify using `[L, hw, Fin.tail]`.

Establish `hwK : w ∈ K` using `by show L w ∈ N`. Rewrite using `[hLw]`. Conclude with `N.sub_mem hv (N.smul_mem t hvoN)`. Establish `hspan : Submodule.span R' {v | v ∈ K ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} ≤ (Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}).comap L`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `w' ⟨hw'K, hw'r⟩`. Conclude with `Submodule.subset_span ⟨hw'K, hLrat w' hw'r⟩`. Establish `h1 : L w ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}` using `hspan (hPK w hwK)`. Establish `h2 : t • vo ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}` using `Submodule.smul_mem _ t (Submodule.subset_span ⟨hvoN, hvorat⟩)`. Establish `: v = L w + t • vo` using `by rw [hLw]; abel`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ h1 h2`. Introduce `u hu`. Establish `h0 : ∀ σ ∈ D, π ^ a ∣ σ (u 0) - u 0`. Introduce `σ hσ`.

Simplify using `using hmemI _ (hu σ hσ)`. Take `⟨c, hc⟩` from `scalar_descent D ϖ hπ hres a (u 0) h0`. Take `⟨t, ht⟩` from `hc`. Take `⟨e, he⟩ : ∃ e : Fin (n + 1) → R', e = Fin.cons (algebraMap R R' c) 0` from `⟨_, rfl⟩`. Establish `herat : ∀ i, e i ∈ Set.range (algebraMap R R')`.

Introduce `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `⟨c, rfl⟩`. Introduce `j`.

Rewrite using `[he]`. Simplify using `using hrat0`. Take `⟨u', hu'⟩ : ∃ u', u' = u - e - t • vo` from `⟨_, rfl⟩`. Take `⟨w, hw⟩ : ∃ w, w = Fin.tail u'` from `⟨_, rfl⟩`. Establish `hLw : L w = u'`.

Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Simplify using `[L, hu', he, hvo0]`. Rewrite using `[ht, hπdef]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `j`. Simplify using `[L, hw, Fin.tail]`. Establish `hwinv : ∀ σ ∈ D, (fun i => σ (w i)) - w ∈ K`. Introduce `σ hσ`. Establish `key : L ((fun i => σ (w i)) - w) = ((fun i => σ (u i)) - u) - (σ t - t) • vo`.

Rewrite using `[L.map_sub, ← hLact, hLw, hu']`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hfix σ _ (herat i), hfix σ _ (hvorat i)]`. Expand and normalize the polynomial expressions, which then agree. Use `show L _ ∈ N`.

Rewrite using `[key]`. Conclude with `N.sub_mem (hu σ hσ) (N.smul_mem _ hvoN)`. Take `⟨a', ha', ha'K⟩` from `hQK w hwinv`. Use `⟨e + L a', fun i => hrat_add _ _ (herat i) (hLrat a' ha' i), ?_⟩` and prove the remaining obligations. Establish `: u - (e + L a') = t • vo + L (w - a')`.

Rewrite using `[L.map_sub, hLw, hu']`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `N.add_mem (N.smul_mem t hvoN) ha'K`.
-/
theorem main_induction [IsDomain R'] [IsDiscreteValuationRing R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hirr : Irreducible (algebraMap R R' ϖ))
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) (r : ℕ) :
    ∀ (n : ℕ) (N : Submodule R' (Fin n → R')), (∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N) →
      (∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) →
      (∀ v ∈ N, v ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}) ∧
      (∀ u : Fin n → R', (∀ σ ∈ D, (fun i => σ (u i)) - u ∈ N) →
        ∃ a : Fin n → R', (∀ i, a i ∈ Set.range (algebraMap R R')) ∧ u - a ∈ N) := by
  have hπ : algebraMap R R' ϖ ≠ 0 := hirr.ne_zero
  have hfix : ∀ (σ : R' ≃ₐ[R] R') (y : R'), y ∈ Set.range (algebraMap R R') → σ y = y := by
    rintro σ y ⟨c, rfl⟩; exact AlgEquiv.commutes σ c
  intro n
  induction n with
  | zero =>
    intro N _ _
    refine ⟨fun v _ => ?_, fun u _ => ⟨0, fun i => i.elim0, ?_⟩⟩
    · have : v = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · have : u - 0 = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
  | succ n ih =>
    intro N hlat hstab
    set π := algebraMap R R' ϖ with hπdef
    let L := consZero (R' := R') n
    have hLact : ∀ (σ : R' ≃ₐ[R] R') (w : Fin n → R'),
        (fun i => σ (L w i)) = L (fun i => σ (w i)) := by
      intro σ w; funext i
      refine Fin.cases ?_ ?_ i <;> simp [L]
    let K := N.comap L
    have hKlat : ∀ w : Fin n → R', π ^ r • w ∈ K := fun w => by
      show L (π ^ r • w) ∈ N
      rw [L.map_smul]; exact hlat _
    have hKstab : ∀ σ ∈ D, ∀ w ∈ K, (fun i => σ (w i)) ∈ K := by
      intro σ hσ w hw
      show L _ ∈ N
      rw [← hLact]; exact hstab σ hσ _ hw
    obtain ⟨hPK, hQK⟩ := ih K hKlat hKstab
    let I : Ideal R' := N.map (LinearMap.proj (R := R') (φ := fun _ : Fin (n + 1) => R') 0)
    have hrI : π ^ r ∈ I := ⟨π ^ r • (fun _ => 1 : Fin (n + 1) → R'), hlat _, by simp⟩
    have hI0 : I ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hrI
      exact pow_ne_zero r hπ hrI
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hirr
    have hmemI : ∀ v ∈ N, π ^ a ∣ v 0 := by
      intro v hv
      have : v 0 ∈ I := ⟨v, hv, rfl⟩
      rw [ha, Ideal.mem_span_singleton] at this
      exact this
    obtain ⟨vs, hvsN, hvs0⟩ : ∃ v ∈ N, v 0 = π ^ a := by
      have : π ^ a ∈ I := by rw [ha]; exact Ideal.subset_span rfl
      obtain ⟨v, hv, hv0⟩ := this
      exact ⟨v, hv, hv0⟩
    have hpa : π ^ a ∈ Set.range (algebraMap R R') := ⟨ϖ ^ a, by simp [hπdef]⟩

    have hvsK : ∀ σ ∈ D, (fun i => σ (Fin.tail vs i)) - Fin.tail vs ∈ K := by
      intro σ hσ
      have e : L ((fun i => σ (Fin.tail vs i)) - Fin.tail vs) = (fun i => σ (vs i)) - vs := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, hvs0, hfix σ _ hpa]
        · intro j; simp [L, Fin.tail]
      show L _ ∈ N
      rw [e]; exact N.sub_mem (hstab σ hσ _ hvsN) hvsN
    obtain ⟨a0, ha0, ha0K⟩ := hQK (Fin.tail vs) hvsK
    obtain ⟨vo, hvo⟩ : ∃ vo, vo = vs - L (Fin.tail vs - a0) := ⟨_, rfl⟩
    have hvoN : vo ∈ N := hvo ▸ N.sub_mem hvsN ha0K
    have hvo0 : vo 0 = π ^ a := by rw [hvo]; simp [L, hvs0]
    have hvorat : ∀ i, vo i ∈ Set.range (algebraMap R R') := by
      intro i
      refine Fin.cases ?_ ?_ i
      · rw [hvo0]; exact hpa
      · intro j
        have : vo j.succ = a0 j := by rw [hvo]; simp [L, Fin.tail]
        rw [this]; exact ha0 j
    have hrat_add : ∀ x y : R', x ∈ Set.range (algebraMap R R') → y ∈ Set.range (algebraMap R R') →
        x + y ∈ Set.range (algebraMap R R') := by
      rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, map_add _ _ _⟩
    have hrat0 : (0 : R') ∈ Set.range (algebraMap R R') := ⟨0, map_zero _⟩
    have hLrat : ∀ w : Fin n → R', (∀ i, w i ∈ Set.range (algebraMap R R')) →
        ∀ i, L w i ∈ Set.range (algebraMap R R') := by
      intro w hw i
      refine Fin.cases ?_ ?_ i
      · simpa [L] using hrat0
      · intro j; simpa [L] using hw j
    refine ⟨?_, ?_⟩
    ·
      intro v hv
      obtain ⟨t, ht⟩ := hmemI v hv
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail (v - t • vo) := ⟨_, rfl⟩
      have hLw : L w = v - t • vo := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, ht, hvo0]; ring
        · intro j; simp [L, hw, Fin.tail]
      have hwK : w ∈ K := by
        show L w ∈ N
        rw [hLw]; exact N.sub_mem hv (N.smul_mem t hvoN)
      have hspan : Submodule.span R' {v | v ∈ K ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} ≤
          (Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}).comap L := by
        rw [Submodule.span_le]
        rintro w' ⟨hw'K, hw'r⟩
        exact Submodule.subset_span ⟨hw'K, hLrat w' hw'r⟩
      have h1 : L w ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        hspan (hPK w hwK)
      have h2 : t • vo ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        Submodule.smul_mem _ t (Submodule.subset_span ⟨hvoN, hvorat⟩)
      have : v = L w + t • vo := by rw [hLw]; abel
      rw [this]; exact Submodule.add_mem _ h1 h2
    ·
      intro u hu
      have h0 : ∀ σ ∈ D, π ^ a ∣ σ (u 0) - u 0 := by
        intro σ hσ; simpa using hmemI _ (hu σ hσ)
      obtain ⟨c, hc⟩ := scalar_descent D ϖ hπ hres a (u 0) h0
      obtain ⟨t, ht⟩ := hc
      obtain ⟨e, he⟩ : ∃ e : Fin (n + 1) → R', e = Fin.cons (algebraMap R R' c) 0 := ⟨_, rfl⟩
      have herat : ∀ i, e i ∈ Set.range (algebraMap R R') := by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [he]; exact ⟨c, rfl⟩
        · intro j; rw [he]; simpa using hrat0
      obtain ⟨u', hu'⟩ : ∃ u', u' = u - e - t • vo := ⟨_, rfl⟩
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail u' := ⟨_, rfl⟩
      have hLw : L w = u' := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, hu', he, hvo0]; rw [ht, hπdef]; ring
        · intro j; simp [L, hw, Fin.tail]
      have hwinv : ∀ σ ∈ D, (fun i => σ (w i)) - w ∈ K := by
        intro σ hσ
        have key : L ((fun i => σ (w i)) - w) = ((fun i => σ (u i)) - u) - (σ t - t) • vo := by
          rw [L.map_sub, ← hLact, hLw, hu']
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
            hfix σ _ (herat i), hfix σ _ (hvorat i)]
          ring
        show L _ ∈ N
        rw [key]; exact N.sub_mem (hu σ hσ) (N.smul_mem _ hvoN)
      obtain ⟨a', ha', ha'K⟩ := hQK w hwinv
      refine ⟨e + L a', fun i => hrat_add _ _ (herat i) (hLrat a' ha' i), ?_⟩
      have : u - (e + L a') = t • vo + L (w - a') := by
        rw [L.map_sub, hLw, hu']; abel
      rw [this]; exact N.add_mem (N.smul_mem t hvoN) ha'K

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hmax : maximalIdeal R' = Ideal.span {algebraMap R R' ϖ}`. Rewrite using `[← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]`. Establish `hirr : Irreducible (algebraMap R R' ϖ)` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax`. Establish `hres' : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) → ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c`.

Introduce `x hx`. Take `⟨c, hc⟩` from `hres x fun σ hσ => by`. Rewrite using `[hmax, Ideal.mem_span_singleton]`. Conclude with `hx σ hσ`. Rewrite `hc` using `[hmax, Ideal.mem_span_singleton]`.

Conclude with `⟨c, hc⟩`. Establish `hmem : algebraMap R R' ϖ ∈ maximalIdeal R'`. Rewrite using `[hmax]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hlat' : ∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N` using `fun w => hlat (Submodule.smul_mem_smul (Ideal.pow_mem_pow hmem r) Submodule.mem_top)`.

Take `⟨hP, -⟩` from `StableLatticeDescent.main_induction D ϖ hirr hres' r n N hlat' hstab`. Conclude with `le_antisymm (fun v hv => hP v hv) (Submodule.span_le.mpr fun v hv => hv.1)`.
-/
theorem stable_lattice_descent_unramified (R R' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    (D : Set (R' ≃ₐ[R] R'))
    (hres : ∀ x : R', (∀ σ ∈ D, σ x - x ∈ maximalIdeal R') →
      ∃ r : R, x - algebraMap R R' r ∈ maximalIdeal R')
    (n r : ℕ) (N : Submodule R' (Fin n → R'))
    (hlat : (maximalIdeal R') ^ r • (⊤ : Submodule R' (Fin n → R')) ≤ N)
    (hstab : ∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) :
    N = Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by
    rw [← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hirr : Irreducible (algebraMap R R' ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hres' : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c := by
    intro x hx
    obtain ⟨c, hc⟩ := hres x fun σ hσ => by
      rw [hmax, Ideal.mem_span_singleton]; exact hx σ hσ
    rw [hmax, Ideal.mem_span_singleton] at hc
    exact ⟨c, hc⟩
  have hmem : algebraMap R R' ϖ ∈ maximalIdeal R' := by
    rw [hmax]; exact Ideal.mem_span_singleton_self _
  have hlat' : ∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N := fun w =>
    hlat (Submodule.smul_mem_smul (Ideal.pow_mem_pow hmem r) Submodule.mem_top)
  obtain ⟨hP, -⟩ :=
    StableLatticeDescent.main_induction D ϖ hirr hres' r n N hlat' hstab
  exact le_antisymm (fun v hv => hP v hv) (Submodule.span_le.mpr fun v hv => hv.1)

end GlobalTheory
