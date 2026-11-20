import Mathlib

namespace BaseChangeColon.Corr

/- English proof (translation)
Rewrite using `[Module.length_eq_coheight, Module.length_eq_coheight]`. Use `Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥` as an intermediate fact. Establish `hb : Ideal.comap (e : S →+* T) ⊥ = ⊥` using `Ideal.comap_bot_of_injective _ e.injective`. Rewrite `this` using `[hb]`. Conclude with `this`.
-/
theorem length_self_eq {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

/- English proof (translation)
Set `S` to `Localization.AtPrime W`. Establish `hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) = J.map (algebraMap R S)`. Rewrite using `[Submodule.localized'_eq_span, Ideal.map]`. Both sides reduce to the same expression. Set `e` to `(IsLocalizedModule.linearEquiv W.primeCompl ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S)) (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S`.

Rewrite using `[← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]`. Conclude with `Module.length_eq_of_surjective Ideal.Quotient.mk_surjective`.
-/
theorem length_loc_quot {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

variable {R R' : Type*} [CommRing R] [CommRing R'] {φ : R →+* R'} {P' : Ideal R'} {s : R}

def sat (h : ∀ r : R', ∃ (n : ℕ) (g : R), φ s ^ n * r - φ g ∈ P') (J : Ideal R) (hJ : P'.comap φ ≤ J) :
    Ideal R' where
  carrier := {x | ∃ n : ℕ, ∃ g ∈ J, φ s ^ n * x - φ g ∈ P'}
  zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨n, g, hg, ha⟩ ⟨m, k, hk, hb⟩
    refine ⟨n + m, s ^ m * g + s ^ n * k, J.add_mem (J.mul_mem_left _ hg) (J.mul_mem_left _ hk), ?_⟩
    have := P'.add_mem (P'.mul_mem_left (φ s ^ m) ha) (P'.mul_mem_left (φ s ^ n) hb)
    convert this using 1
    simp only [map_add, map_mul, map_pow]
    ring
  smul_mem' := by
    rintro c x ⟨n, g, hg, hx⟩
    obtain ⟨m, k, hc⟩ := h c
    refine ⟨n + m, k * g, J.mul_mem_left _ hg, ?_⟩
    have := P'.add_mem (P'.mul_mem_left (φ s ^ m * c) hx) (P'.mul_mem_left (φ g) hc)
    convert this using 1
    simp only [map_mul, smul_eq_mul]
    ring

/- English proof (translation)
Establish `hle : P' ⊔ J.map φ ≤ sat h J hJ`. Use `sup_le (fun y hy => ⟨0, 0, J.zero_mem, by simpa using hy⟩) (Ideal.map_le_iff_le_comap.2 ?_)` and prove the remaining obligations. Introduce `g hg`. Conclude with `⟨0, g, hg, by simp⟩`. Conclude with `hle hx`.
-/
theorem key (h : ∀ r : R', ∃ (n : ℕ) (g : R), φ s ^ n * r - φ g ∈ P') (J : Ideal R) (hJ : P'.comap φ ≤ J)
    {x : R'} (hx : x ∈ P' ⊔ J.map φ) : ∃ n : ℕ, ∃ g ∈ J, φ s ^ n * x - φ g ∈ P' := by
  have hle : P' ⊔ J.map φ ≤ sat h J hJ := by
    refine sup_le (fun y hy => ⟨0, 0, J.zero_mem, by simpa using hy⟩) (Ideal.map_le_iff_le_comap.2 ?_)
    intro g hg
    exact ⟨0, g, hg, by simp⟩
  exact hle hx

/- English proof (translation)
Take `⟨n, g, hg, hn⟩` from `key h J hJ ht`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h1 : s ^ n * t - g ∈ J` using `hJ (by`. Rewrite using `[Ideal.mem_comap, map_sub, map_mul, map_pow]`. Conclude with `hn)`.

Simplify using `using J.add_mem h1 hg`.
-/
theorem key' (h : ∀ r : R', ∃ (n : ℕ) (g : R), φ s ^ n * r - φ g ∈ P') (J : Ideal R) (hJ : P'.comap φ ≤ J)
    {t : R} (ht : φ t ∈ P' ⊔ J.map φ) : ∃ n : ℕ, s ^ n * t ∈ J := by
  obtain ⟨n, g, hg, hn⟩ := key h J hJ ht
  refine ⟨n, ?_⟩
  have h1 : s ^ n * t - g ∈ J := hJ (by
    rw [Ideal.mem_comap, map_sub, map_mul, map_pow]
    exact hn)
  simpa using J.add_mem h1 hg

/- English proof (translation)
Introduce `r hr`. Take `⟨n, g, hg⟩` from `h r`. Establish `h1 : φ g ∈ Q`. Use `Q.sub_mem (Q.mul_mem_left (φ s ^ n) hr) (hPQ hg)` as an intermediate fact. Simplify using `using this`.

Establish `h2 : φ g ∈ W` using `hle h1`. Establish `h3 : φ s ^ n * r ∈ W`. Simplify using `using W.add_mem (hPW hg) h2`. Conclude with `(hW.mem_or_mem h3).resolve_left fun h4 => hs (hW.mem_of_pow_mem _ h4)`.
-/
theorem mono (h : ∀ r : R', ∃ (n : ℕ) (g : R), φ s ^ n * r - φ g ∈ P') {Q W : Ideal R'} (hW : W.IsPrime)
    (hPQ : P' ≤ Q) (hPW : P' ≤ W) (hs : φ s ∉ W) (hle : Q.comap φ ≤ W.comap φ) : Q ≤ W := by
  intro r hr
  obtain ⟨n, g, hg⟩ := h r
  have h1 : φ g ∈ Q := by
    have := Q.sub_mem (Q.mul_mem_left (φ s ^ n) hr) (hPQ hg)
    simpa using this
  have h2 : φ g ∈ W := hle h1
  have h3 : φ s ^ n * r ∈ W := by
    simpa using W.add_mem (hPW hg) h2
  exact (hW.mem_or_mem h3).resolve_left fun h4 => hs (hW.mem_of_pow_mem _ h4)

/- English proof (translation)
Establish `hd : Disjoint ((P' ⊔ W.map φ : Ideal R') : Set R') (W.primeCompl.map φ : Submonoid R')`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ hx ⟨t, ht, rfl⟩`. Take `⟨n, hn⟩` from `key' h W hPW hx`. Break down `hW.mem_or_mem hn with h1 | h1` into its components or cases.

Conclude with `hs (hW.mem_of_pow_mem _ h1)`. Conclude with `ht h1`. Take `⟨W', hW', hle, hdis⟩` from `Ideal.exists_le_prime_disjoint _ _ hd`. Use `⟨W', hW', le_sup_left.trans hle, le_antisymm (fun t ht => ?_) (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hle))⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Conclude with `Set.disjoint_left.1 hdis (show φ t ∈ (W' : Set R') from ht) ⟨t, hn, rfl⟩`.
-/
theorem exists_lift (h : ∀ r : R', ∃ (n : ℕ) (g : R), φ s ^ n * r - φ g ∈ P') {W : Ideal R} (hW : W.IsPrime)
    (hPW : P'.comap φ ≤ W) (hs : s ∉ W) :
    ∃ W' : Ideal R', W'.IsPrime ∧ P' ≤ W' ∧ W'.comap φ = W := by
  have hd : Disjoint ((P' ⊔ W.map φ : Ideal R') : Set R') (W.primeCompl.map φ : Submonoid R') := by
    rw [Set.disjoint_left]
    rintro _ hx ⟨t, ht, rfl⟩
    obtain ⟨n, hn⟩ := key' h W hPW hx
    rcases hW.mem_or_mem hn with h1 | h1
    · exact hs (hW.mem_of_pow_mem _ h1)
    · exact ht h1
  obtain ⟨W', hW', hle, hdis⟩ := Ideal.exists_le_prime_disjoint _ _ hd
  refine ⟨W', hW', le_sup_left.trans hle, le_antisymm (fun t ht => ?_)
    (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hle))⟩
  by_contra hn
  exact Set.disjoint_left.1 hdis (show φ t ∈ (W' : Set R') from ht) ⟨t, hn, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, hle⟩, hmin⟩`. Use `⟨⟨Ideal.comap_isPrime φ W', Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hle)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Q ⟨hQ, hJQ⟩ hQW`. Take `⟨Q', hQ', hPQ', rfl⟩` from `exists_lift h hQ (hJ.trans hJQ) fun hq => hs (hQW hq)`.

Establish `h1 : Q' ≤ W'` using `mono h hW' hPQ' hPW hs hQW`. Conclude with `Ideal.comap_mono (hmin ⟨hQ', sup_le hPQ' (Ideal.map_le_iff_le_comap.2 hJQ)⟩ h1)`. Introduce and unpack `⟨⟨-, hle⟩, hmin⟩`. Use `⟨⟨hW', sup_le hPW (Ideal.map_le_iff_le_comap.2 hle)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Q' ⟨hQ', hJQ⟩ hQW`.

Establish `h1 : W'.comap φ ≤ Q'.comap φ` using `hmin ⟨Ideal.comap_isPrime φ Q', Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hJQ)⟩ (Ideal.comap_mono hQW)`. Conclude with `mono h hQ' hPW (le_sup_left.trans hJQ) (fun hq => hs (hQW hq)) h1`.
-/
theorem minimal_iff (h : ∀ r : R', ∃ (n : ℕ) (g : R), φ s ^ n * r - φ g ∈ P') (J : Ideal R)
    (hJ : P'.comap φ ≤ J) {W' : Ideal R'} (hW' : W'.IsPrime) (hPW : P' ≤ W') (hs : φ s ∉ W') :
    W' ∈ (P' ⊔ J.map φ).minimalPrimes ↔ W'.comap φ ∈ J.minimalPrimes := by
  constructor
  · rintro ⟨⟨-, hle⟩, hmin⟩
    refine ⟨⟨Ideal.comap_isPrime φ W', Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hle)⟩, ?_⟩
    rintro Q ⟨hQ, hJQ⟩ hQW
    obtain ⟨Q', hQ', hPQ', rfl⟩ := exists_lift h hQ (hJ.trans hJQ) fun hq => hs (hQW hq)
    have h1 : Q' ≤ W' := mono h hW' hPQ' hPW hs hQW
    exact Ideal.comap_mono (hmin ⟨hQ', sup_le hPQ' (Ideal.map_le_iff_le_comap.2 hJQ)⟩ h1)
  · rintro ⟨⟨-, hle⟩, hmin⟩
    refine ⟨⟨hW', sup_le hPW (Ideal.map_le_iff_le_comap.2 hle)⟩, ?_⟩
    rintro Q' ⟨hQ', hJQ⟩ hQW
    have h1 : W'.comap φ ≤ Q'.comap φ :=
      hmin ⟨Ideal.comap_isPrime φ Q', Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hJQ)⟩
        (Ideal.comap_mono hQW)
    exact mono h hQ' hPW (le_sup_left.trans hJQ) (fun hq => hs (hQW hq)) h1

/- English proof (translation)
Rewrite using `[length_loc_quot, length_loc_quot]`. Establish `hmem : ∀ {x : R}, x ∈ W ↔ φ x ∈ W'`. Introduce `x`. Rewrite using `[hWW, Ideal.mem_comap]`. Establish `hsW : s ∉ W` using `fun hh => hs (hmem.1 hh)`.

Establish `hspow : ∀ n : ℕ, φ s ^ n ∉ W'` using `fun n hh => hs (hW'.mem_of_pow_mem _ hh)`. Set `ψ : Localization.AtPrime W →+* Localization.AtPrime W'` to `Localization.localRingHom W W' φ hWW`. Establish `hψ : ∀ x, ψ (algebraMap R _ x) = algebraMap R' _ (φ x)` using `fun x => Localization.localRingHom_to_map W W' φ hWW x`. Take `⟨I', hI'⟩ : ∃ I', I' = (P' ⊔ J.map φ).map (algebraMap R' (Localization.AtPrime W'))` from `⟨_, rfl⟩`. Establish `hPI : ∀ {x}, x ∈ P' → algebraMap R' (Localization.AtPrime W') x ∈ I'`.

Introduce `x hx`. Rewrite using `[hI']`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hx)`. Set `g` to `(Ideal.Quotient.mk I').comp ψ`. Establish `hunit : ∀ t, t ∉ W' → ∃ u : Localization.AtPrime W, IsUnit u ∧ g u = Ideal.Quotient.mk I' (algebraMap R' _ t)`.

Introduce `t ht`. Take `⟨n, k, hk⟩` from `h t`. Establish `hkW : k ∉ W`. Introduce `hh`. Establish `h3 : φ s ^ n * t ∈ W'` using `by simpa using W'.add_mem (hPW hk) (hmem.1 hh)`.

Conclude with `(hW'.mem_or_mem h3).elim (hspow n) ht`. Establish `hsn : s ^ n ∈ W.primeCompl` using `W.primeCompl.pow_mem hsW n`. Use `⟨IsLocalization.mk' _ k ⟨s ^ n, hsn⟩, (IsLocalization.AtPrime.isUnit_mk'_iff _ W k _).2 hkW, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (g (algebraMap R (Localization.AtPrime W) (s ^ n)))` using `(IsLocalization.map_units (Localization.AtPrime W) ⟨s ^ n, hsn⟩).map g`. Use `hu.mul_left_cancel ?_` and prove the remaining obligations.

Rewrite using `[← map_mul, IsLocalization.mk'_spec' (Localization.AtPrime W) k ⟨s ^ n, hsn⟩]`. Simplify using `only [g, RingHom.comp_apply, hψ]`. Rewrite using `[← map_mul, ← map_mul, eq_comm, Ideal.Quotient.eq, ← map_sub, map_pow]`. Conclude with `hPI hk`. Establish `hall : ∀ r : R', ∃ u : Localization.AtPrime W, g u = Ideal.Quotient.mk I' (algebraMap R' _ r)`.

Introduce `r`. Distinguish the cases in `hr : r ∈ W'`. Establish `h1 : 1 + r ∉ W'` using `fun hh => hW'.ne_top ((Ideal.eq_top_iff_one _).2 (by`. Simplify using `using W'.sub_mem hh hr))`. Take `⟨u, -, hu⟩` from `hunit _ h1`.

Use `⟨u - 1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hu, map_one, map_add, map_add, map_one, map_one]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u, -, hu⟩` from `hunit _ hr`. Conclude with `⟨u, hu⟩`.

Establish `hg : Function.Surjective g`. Introduce `z`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨⟨r, t⟩, hrt⟩` from `IsLocalization.surj W'.primeCompl x`. Take `⟨a, ha⟩` from `hall r`.

Take `⟨u, ⟨u, rfl⟩, hu⟩` from `hunit t.1 t.2`. Use `⟨a * (u⁻¹ : (Localization.AtPrime W)ˣ), ?_⟩` and prove the remaining obligations. Establish `hrt' : x * algebraMap R' (Localization.AtPrime W') t.1 = algebraMap R' _ r` using `hrt`. Rewrite using `[map_mul, ha, ← hrt', map_mul, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]`. Establish `hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Simplify using `only [g, RingHom.comp_apply, hψ]`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hI']`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx))`. Introduce `x hx`. Take `⟨⟨r, t⟩, hrt⟩` from `IsLocalization.surj W.primeCompl x`. Establish `hrt' : x * algebraMap R (Localization.AtPrime W) t.1 = algebraMap R _ r` using `hrt`.

Establish `h1 : algebraMap R (Localization.AtPrime W) r ∈ RingHom.ker g`. Rewrite using `[← hrt']`. Conclude with `Ideal.mul_mem_right _ _ hx`. Rewrite `h1` using `[RingHom.mem_ker]`. Simplify using `only [g, RingHom.comp_apply, hψ] at h1`.

Rewrite `h1` using `[Ideal.Quotient.eq_zero_iff_mem, hI', IsLocalization.algebraMap_mem_map_algebraMap_iff W'.primeCompl]`. Take `⟨t', ht', h2⟩` from `h1`. Take `⟨n, k, hk⟩` from `h t'`. Establish `hkW : k ∉ W`. Introduce `hh`.

Establish `h3 : φ s ^ n * t' ∈ W'` using `by simpa using W'.add_mem (hPW hk) (hmem.1 hh)`. Conclude with `(hW'.mem_or_mem h3).elim (hspow n) ht'`. Establish `h4 : φ (k * r) ∈ P' ⊔ J.map φ`. Use `(P' ⊔ J.map φ).sub_mem ((P' ⊔ J.map φ).mul_mem_left (φ s ^ n) h2) ((P' ⊔ J.map φ).mul_mem_left (φ r) (Ideal.mem_sup_left hk))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm⟩` from `key' h J hJ h4`. Establish `h5 : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W))`. Rewrite using `[IsLocalization.algebraMap_mem_map_algebraMap_iff W.primeCompl]`.

Conclude with `⟨s ^ m * k, W.primeCompl.mul_mem (W.primeCompl.pow_mem hsW m) hkW, by`. Rewrite using `[mul_assoc]`. Conclude with `hm⟩`. Rewrite `h5` using `[← hrt']`. Conclude with `(Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) t)).1 h5`.

Establish `key` using `length_self_eq ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))`. Rewrite using `[key, hI']`.
-/
theorem length_eq (h : ∀ r : R', ∃ (n : ℕ) (g : R), φ s ^ n * r - φ g ∈ P') (J : Ideal R)
    (hJ : P'.comap φ ≤ J) (W' : Ideal R') [hW' : W'.IsPrime] (W : Ideal R) [hW : W.IsPrime]
    (hWW : W = W'.comap φ) (hPW : P' ≤ W') (hs : φ s ∉ W') :
    Module.length (Localization.AtPrime W') (LocalizedModule W'.primeCompl (R' ⧸ (P' ⊔ J.map φ))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) := by
  rw [length_loc_quot, length_loc_quot]
  have hmem : ∀ {x : R}, x ∈ W ↔ φ x ∈ W' := by
    intro x
    rw [hWW, Ideal.mem_comap]
  have hsW : s ∉ W := fun hh => hs (hmem.1 hh)
  have hspow : ∀ n : ℕ, φ s ^ n ∉ W' := fun n hh => hs (hW'.mem_of_pow_mem _ hh)
  let ψ : Localization.AtPrime W →+* Localization.AtPrime W' := Localization.localRingHom W W' φ hWW
  have hψ : ∀ x, ψ (algebraMap R _ x) = algebraMap R' _ (φ x) :=
    fun x => Localization.localRingHom_to_map W W' φ hWW x
  obtain ⟨I', hI'⟩ : ∃ I', I' = (P' ⊔ J.map φ).map (algebraMap R' (Localization.AtPrime W')) := ⟨_, rfl⟩
  have hPI : ∀ {x}, x ∈ P' → algebraMap R' (Localization.AtPrime W') x ∈ I' := by
    intro x hx
    rw [hI']
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hx)
  let g := (Ideal.Quotient.mk I').comp ψ

  have hunit : ∀ t, t ∉ W' → ∃ u : Localization.AtPrime W, IsUnit u ∧
      g u = Ideal.Quotient.mk I' (algebraMap R' _ t) := by
    intro t ht
    obtain ⟨n, k, hk⟩ := h t
    have hkW : k ∉ W := by
      intro hh
      have h3 : φ s ^ n * t ∈ W' := by simpa using W'.add_mem (hPW hk) (hmem.1 hh)
      exact (hW'.mem_or_mem h3).elim (hspow n) ht
    have hsn : s ^ n ∈ W.primeCompl := W.primeCompl.pow_mem hsW n
    refine ⟨IsLocalization.mk' _ k ⟨s ^ n, hsn⟩,
      (IsLocalization.AtPrime.isUnit_mk'_iff _ W k _).2 hkW, ?_⟩
    have hu : IsUnit (g (algebraMap R (Localization.AtPrime W) (s ^ n))) :=
      (IsLocalization.map_units (Localization.AtPrime W) ⟨s ^ n, hsn⟩).map g
    refine hu.mul_left_cancel ?_
    rw [← map_mul, IsLocalization.mk'_spec' (Localization.AtPrime W) k ⟨s ^ n, hsn⟩]
    simp only [g, RingHom.comp_apply, hψ]
    rw [← map_mul, ← map_mul, eq_comm, Ideal.Quotient.eq, ← map_sub, map_pow]
    exact hPI hk
  have hall : ∀ r : R', ∃ u : Localization.AtPrime W,
      g u = Ideal.Quotient.mk I' (algebraMap R' _ r) := by
    intro r
    by_cases hr : r ∈ W'
    · have h1 : 1 + r ∉ W' := fun hh => hW'.ne_top ((Ideal.eq_top_iff_one _).2 (by
        simpa using W'.sub_mem hh hr))
      obtain ⟨u, -, hu⟩ := hunit _ h1
      refine ⟨u - 1, ?_⟩
      rw [map_sub, hu, map_one, map_add, map_add, map_one, map_one]
      ring
    · obtain ⟨u, -, hu⟩ := hunit _ hr
      exact ⟨u, hu⟩
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj W'.primeCompl x
    obtain ⟨a, ha⟩ := hall r
    obtain ⟨u, ⟨u, rfl⟩, hu⟩ := hunit t.1 t.2
    refine ⟨a * (u⁻¹ : (Localization.AtPrime W)ˣ), ?_⟩
    have hrt' : x * algebraMap R' (Localization.AtPrime W') t.1 = algebraMap R' _ r := hrt
    rw [map_mul, ha, ← hrt', map_mul, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simp only [g, RingHom.comp_apply, hψ]
      rw [Ideal.Quotient.eq_zero_iff_mem, hI']
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx))
    · intro x hx
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj W.primeCompl x
      have hrt' : x * algebraMap R (Localization.AtPrime W) t.1 = algebraMap R _ r := hrt
      have h1 : algebraMap R (Localization.AtPrime W) r ∈ RingHom.ker g := by
        rw [← hrt']
        exact Ideal.mul_mem_right _ _ hx
      rw [RingHom.mem_ker] at h1
      simp only [g, RingHom.comp_apply, hψ] at h1
      rw [Ideal.Quotient.eq_zero_iff_mem, hI',
        IsLocalization.algebraMap_mem_map_algebraMap_iff W'.primeCompl] at h1
      obtain ⟨t', ht', h2⟩ := h1
      obtain ⟨n, k, hk⟩ := h t'
      have hkW : k ∉ W := by
        intro hh
        have h3 : φ s ^ n * t' ∈ W' := by simpa using W'.add_mem (hPW hk) (hmem.1 hh)
        exact (hW'.mem_or_mem h3).elim (hspow n) ht'
      have h4 : φ (k * r) ∈ P' ⊔ J.map φ := by
        have := (P' ⊔ J.map φ).sub_mem ((P' ⊔ J.map φ).mul_mem_left (φ s ^ n) h2)
          ((P' ⊔ J.map φ).mul_mem_left (φ r) (Ideal.mem_sup_left hk))
        convert this using 1
        rw [map_mul]
        ring
      obtain ⟨m, hm⟩ := key' h J hJ h4
      have h5 : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W)) := by
        rw [IsLocalization.algebraMap_mem_map_algebraMap_iff W.primeCompl]
        exact ⟨s ^ m * k, W.primeCompl.mul_mem (W.primeCompl.pow_mem hsW m) hkW, by
          rw [mul_assoc]; exact hm⟩
      rw [← hrt'] at h5
      exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) t)).1 h5
  have key := length_self_eq
    ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [key, hI']

end BaseChangeColon.Corr
