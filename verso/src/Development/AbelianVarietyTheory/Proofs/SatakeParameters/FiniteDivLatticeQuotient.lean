import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : I ⊔ (⨅ P ∈ S, P.asIdeal) = ⊤`. Use `Ideal.sup_iInf_eq_top fun P hP => ?_` and prove the remaining obligations. Take `⟨s, hs, hsP⟩` from `hI P hP`. Assume the negation of the conclusion as `hne`. Use `P.isMaximal.eq_of_le hne le_sup_right` as an intermediate fact.

Conclude with `hsP (this ▸ (le_sup_left : I ≤ I ⊔ P.asIdeal) hs)`. Establish `h2 : (1 : R) ∈ I ⊔ (⨅ P ∈ S, P.asIdeal)` using `h1 ▸ Submodule.mem_top`. Take `⟨s0, hs0, π, hπ, hsum⟩` from `Submodule.mem_sup.1 h2`. Establish `hπ' : ∀ P ∈ S, π ∈ P.asIdeal`. Introduce `P hP`.

Conclude with `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hπ P) hP`. Establish `key : ∃ i j : ℕ, i < j ∧ Ideal.Quotient.mk (Ideal.span {c}) (π ^ i) = Ideal.Quotient.mk (Ideal.span {c}) (π ^ j)`. Take `⟨i, j, hij, h⟩` from `Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => Ideal.Quotient.mk (Ideal.span {c}) (π ^ i))`. Break down `lt_or_gt_of_ne hij with h' | h'` into its components or cases. Conclude with `⟨i, j, h', h⟩`.

Conclude with `⟨j, i, h', h.symm⟩`. Take `⟨i, j, hij, h⟩` from `key`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hij`. Use `⟨1 - π ^ i, ?_, 1 - π ^ (d + 1), r, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (1 - π) ∣ 1 - π ^ i` using `by simpa using sub_dvd_pow_sub_pow (1 : R) π i`. Take `⟨u, hu⟩` from `this`. Establish `hs : 1 - π = s0` using `by rw [← hsum]; ring`. Rewrite using `[hu, hs]`. Conclude with `I.mul_mem_right _ hs0`.

Introduce `P hP hmem`. Establish `: π ^ (d + 1) ∈ P.asIdeal` using `P.asIdeal.pow_mem_of_mem (hπ' P hP) _ (Nat.succ_pos d)`. Establish `h1 : (1 : R) ∈ P.asIdeal` using `by simpa using P.asIdeal.add_mem hmem this`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Rewrite using `[← hr]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mem_one_sub_loc_dvd {R : Type} [CommRing R] [IsDedekindDomain R] (S : Finset (HeightOneSpectrum R))
    (I : Ideal R) (hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal) (c : R) [Finite (R ⧸ Ideal.span {c})] :
    ∃ s ∈ I, ∃ t r : R, (∀ P ∈ S, t ∉ P.asIdeal) ∧ t * (1 - s) = c * r := by
  have h1 : I ⊔ (⨅ P ∈ S, P.asIdeal) = ⊤ := by
    refine Ideal.sup_iInf_eq_top fun P hP => ?_
    obtain ⟨s, hs, hsP⟩ := hI P hP
    by_contra hne
    have := P.isMaximal.eq_of_le hne le_sup_right
    exact hsP (this ▸ (le_sup_left : I ≤ I ⊔ P.asIdeal) hs)
  have h2 : (1 : R) ∈ I ⊔ (⨅ P ∈ S, P.asIdeal) := h1 ▸ Submodule.mem_top
  obtain ⟨s0, hs0, π, hπ, hsum⟩ := Submodule.mem_sup.1 h2
  have hπ' : ∀ P ∈ S, π ∈ P.asIdeal := by
    intro P hP
    exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hπ P) hP
  have key : ∃ i j : ℕ, i < j ∧ Ideal.Quotient.mk (Ideal.span {c}) (π ^ i) = Ideal.Quotient.mk (Ideal.span {c}) (π ^ j) := by
    obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun i : ℕ => Ideal.Quotient.mk (Ideal.span {c}) (π ^ i))
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact ⟨i, j, h', h⟩
    · exact ⟨j, i, h', h.symm⟩
  obtain ⟨i, j, hij, h⟩ := key
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨1 - π ^ i, ?_, 1 - π ^ (d + 1), r, ?_, ?_⟩
  · have : (1 - π) ∣ 1 - π ^ i := by simpa using sub_dvd_pow_sub_pow (1 : R) π i
    obtain ⟨u, hu⟩ := this
    have hs : 1 - π = s0 := by rw [← hsum]; ring
    rw [hu, hs]
    exact I.mul_mem_right _ hs0
  · intro P hP hmem
    have : π ^ (d + 1) ∈ P.asIdeal := P.asIdeal.pow_mem_of_mem (hπ' P hP) _ (Nat.succ_pos d)
    have h1 : (1 : R) ∈ P.asIdeal := by simpa using P.asIdeal.add_mem hmem this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rw [← hr]; ring

/- English proof (translation)
Introduce `E _ _ _ a b S N N' cA cB hN hN' hA hB`. Take `⟨G, hG⟩` from `hN.fg`. Establish `hA' : (cA : E) ≠ 0` using `by exact_mod_cast hA.ne'`. Establish `hB' : (cB : E) ≠ 0` using `by exact_mod_cast hB.ne'`. Establish `memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔ ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N'` using `fun x => Iff.rfl`.

Establish `memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔ ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x` using `fun x => Iff.rfl`. Establish `memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔ ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N'` using `fun x => Iff.rfl`. Set `ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b)` to `{ toFun := fun x g => (cA : 𝓞 E) • x g map_add' := by intro x y; funext g; simp map_smul' := by intro r x; funext g; simp [smul_comm r] }`. Establish `ev_inj : Function.Injective ev`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `hsp : Submodule.span E (G : Set (Sp E a)) = ⊤`. Rewrite using `[← hN.span_eq_top, ← hG, Submodule.span_span_of_tower]`. Use `LinearMap.ext_on hsp fun g hg => ?_` and prove the remaining obligations. Use `congrFun hx ⟨g, hg⟩` as an intermediate fact.

Establish `h2 : (cA : E) • x g = 0`. Rewrite using `[Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `this`. Simplify `(smul_eq_zero.1 h2).resolve_left hA'` using `[hA']`. Set `T : Submodule (𝓞 E) (G → Sp E b)` to `Submodule.pi Set.univ fun _ => N'`.

Establish `hT : T.FG` using `Submodule.fg_pi fun _ => hN'.fg`. Set `Z : Submodule (𝓞 E) (HomE E a b)` to `T.comap ev`. Establish `memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N'` using `fun x => ⟨fun h g => h g trivial, fun h g _ => h g⟩`. Establish `hZ : Z.FG`. Establish `: Module.Finite (𝓞 E) T` using `Module.Finite.iff_fg.2 hT`.

Establish `: Module.Finite (𝓞 E) Z` using `Module.Finite.of_injective (ev.restrict (p := Z) (q := T) fun x hx => hx) (by`. Introduce `x y hxy`. Conclude with `Subtype.ext (ev_inj (congrArg Subtype.val hxy)))`. Conclude with `Module.Finite.iff_fg.1 this`. Establish `hZD : Z ≤ divLat cA (homAt S N N')`.

Introduce `x hx`. Rewrite using `[memD]`. Introduce `P hP y hy`. Take `⟨s, hs, hsy⟩` from `(mem_locP P N y).1 hy`. Establish `: ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N'`.

Introduce `w hw`. Rewrite `hw` using `[← hG]`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem g hg => exact (memZ x).1 hx ⟨g, hg⟩`. Consider the case `zero => simp`.

Consider the case `add u v _ _ hu hv => rw [map_add, smul_add]`. Conclude with `N'.add_mem hu hv`. Consider the case `smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]`. Conclude with `N'.smul_mem r hu`. Use `(mem_locP P N' _).2 ⟨s, hs, ?_⟩` and prove the remaining obligations.

Establish `h` using `this _ hsy`. Rewrite `h` using `[LinearMap.map_smul_of_tower, smul_comm]`. Then use the resulting hypothesis. Establish `: Module.Finite (𝓞 E) Z` using `Module.Finite.iff_fg.2 hZ`. Establish `hc : ((cB : 𝓞 E) * cA) ≠ 0`. Establish `: cB * cA ≠ 0` using `by positivity`.

Conclude with `this` after adjusting the coercions. Establish `: Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA})` using `Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)`. Establish `hsurj : Function.Surjective (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD)`. Introduce `q`. Take `⟨⟨x, hx⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Set `I : Ideal (𝓞 E)` to `Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)`. Establish `hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal`. Introduce `P hP`. Establish `h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N'` using `fun g => (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))`. Use `choose f hf hf' using h1`.

Use `⟨∏ g, f g, ?_, ?_⟩` and prove the remaining obligations. Use `show (∏ g, f g) • x ∈ Z`. Rewrite using `[memZ]`. Introduce `g`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]`.

Conclude with `N'.smul_mem _ (hf' g)`. Introduce `h`. Use `P.isPrime` as an intermediate fact. Take `⟨g, _, hg⟩` from `Ideal.IsPrime.prod_mem_iff.1 h`. Conclude with `hf g hg`.

Take `⟨s, hs, t, r, ht, htr⟩` from `exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)`. Use `⟨⟨s • x, hs⟩, ?_⟩` and prove the remaining obligations. Use `symm`. Use `(Submodule.Quotient.eq _).2 ?_` and prove the remaining obligations. Use `show x - s • x ∈ mulLat cB (homAt S N N')`.

Establish `hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W), (cB : 𝓞 E) • (cB : E)⁻¹ • w = w`. Introduce `W _ _ _ w`. Rewrite using `[Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]`. Rewrite using `[memM]`. Use `⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩` and prove the remaining obligations.

Rewrite using `[memH]`. Introduce `P hP y hy`. Take `⟨u, hu, huy⟩` from `(mem_locP P N' _).1 ((memD x).1 hx P hP y hy)`. Use `(mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩` and prove the remaining obligations. Establish `e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y`.

Establish `e2 : (x - s • x) y = (1 - s) • x y` using `by simp [sub_smul]`. Rewrite using `[LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]`. Rewrite using `[mul_smul, e1, smul_comm]`. Conclude with `N'.smul_mem r huy`. Use `Module.Finite.of_surjective _ hsurj` as an intermediate fact.

Establish `: Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)` using `Module.Finite.trans (𝓞 E) _`. Use `Module.finite_of_fg_torsion _ ?_` and prove the remaining obligations. Introduce `q`. Take `⟨⟨x, hx⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Use `⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')`. Rewrite using `[memM]`. Conclude with `⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩`.
-/
theorem finite_divLat_quot_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA cB : ℕ), Submodule.IsLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < cB → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) := by
  intro E _ _ _ a b S N N' cA cB hN hN' hA hB
  classical
  obtain ⟨G, hG⟩ := hN.fg
  have hA' : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (cB : E) ≠ 0 := by exact_mod_cast hB.ne'
  have memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  have memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔
      ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x := fun x => Iff.rfl
  have memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  let ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b) :=
    { toFun := fun x g => (cA : 𝓞 E) • x g
      map_add' := by intro x y; funext g; simp
      map_smul' := by intro r x; funext g; simp [smul_comm r] }
  have ev_inj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hsp : Submodule.span E (G : Set (Sp E a)) = ⊤ := by
      rw [← hN.span_eq_top, ← hG, Submodule.span_span_of_tower]
    refine LinearMap.ext_on hsp fun g hg => ?_
    have := congrFun hx ⟨g, hg⟩
    have h2 : (cA : E) • x g = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact this
    simpa [hA'] using (smul_eq_zero.1 h2).resolve_left hA'
  let T : Submodule (𝓞 E) (G → Sp E b) := Submodule.pi Set.univ fun _ => N'
  have hT : T.FG := Submodule.fg_pi fun _ => hN'.fg
  let Z : Submodule (𝓞 E) (HomE E a b) := T.comap ev
  have memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N' := fun x =>
    ⟨fun h g => h g trivial, fun h g _ => h g⟩
  have hZ : Z.FG := by
    have : Module.Finite (𝓞 E) T := Module.Finite.iff_fg.2 hT
    have : Module.Finite (𝓞 E) Z := Module.Finite.of_injective (ev.restrict (p := Z) (q := T) fun x hx => hx) (by
      intro x y hxy
      exact Subtype.ext (ev_inj (congrArg Subtype.val hxy)))
    exact Module.Finite.iff_fg.1 this
  have hZD : Z ≤ divLat cA (homAt S N N') := by
    intro x hx
    rw [memD]
    intro P hP y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
    have : ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N' := by
      intro w hw
      rw [← hG] at hw
      induction hw using Submodule.span_induction with
      | mem g hg => exact (memZ x).1 hx ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, smul_add]; exact N'.add_mem hu hv
      | smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]; exact N'.smul_mem r hu
    refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
    have h := this _ hsy
    rwa [LinearMap.map_smul_of_tower, smul_comm] at h
  have : Module.Finite (𝓞 E) Z := Module.Finite.iff_fg.2 hZ
  have hc : ((cB : 𝓞 E) * cA) ≠ 0 := by
    have : cB * cA ≠ 0 := by positivity
    exact_mod_cast this
  have : Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)
  have hsurj : Function.Surjective
      (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let I : Ideal (𝓞 E) := Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
    have hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal := by
      intro P hP
      have h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N' := fun g =>
        (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))
      choose f hf hf' using h1
      refine ⟨∏ g, f g, ?_, ?_⟩
      · show (∏ g, f g) • x ∈ Z
        rw [memZ]
        intro g
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]
        exact N'.smul_mem _ (hf' g)
      · intro h
        have := P.isPrime
        obtain ⟨g, _, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
        exact hf g hg
    obtain ⟨s, hs, t, r, ht, htr⟩ := exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)
    refine ⟨⟨s • x, hs⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show x - s • x ∈ mulLat cB (homAt S N N')
    have hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W),
        (cB : 𝓞 E) • (cB : E)⁻¹ • w = w := by
      intro W _ _ _ w
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩
    rw [memH]
    intro P hP y hy
    obtain ⟨u, hu, huy⟩ := (mem_locP P N' _).1 ((memD x).1 hx P hP y hy)
    refine (mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩
    have e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y := by
      have e2 : (x - s • x) y = (1 - s) • x y := by simp [sub_smul]
      rw [LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]
    rw [mul_smul, e1, smul_comm]
    exact N'.smul_mem r huy
  have := Module.Finite.of_surjective _ hsurj
  have : Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
    Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
  rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')
  rw [memM]
  exact ⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩

end GlobalTheory
