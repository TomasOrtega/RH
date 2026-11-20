import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Establish `h1 : ZMod.castHom h (ZMod d) (idem r N) = 1`. Unfold `idem`. Rewrite using `[map_natCast, ← Nat.cast_one (R := ZMod d), ZMod.natCast_eq_natCast_iff]`. Conclude with `(Nat.ModEq.pow_totient (coprime_ordProj_ordCompl r N).symm).of_dvd hd`. Apply `Units.ext` to reduce the goal to its premises.

Use `show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = ZMod.castHom h (ZMod d) u`. Rewrite using `[map_add, map_mul, map_sub, h1, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem projA {N : ℕ} (r d : ℕ) (h : d ∣ N) (hd : d ∣ ordProj[r] N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h (proj r N u) = ZMod.unitsMap h u := by
  have h1 : ZMod.castHom h (ZMod d) (idem r N) = 1 := by
    unfold idem
    rw [map_natCast, ← Nat.cast_one (R := ZMod d), ZMod.natCast_eq_natCast_iff]
    exact (Nat.ModEq.pow_totient (coprime_ordProj_ordCompl r N).symm).of_dvd hd
  apply Units.ext
  show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = ZMod.castHom h (ZMod d) u
  rw [map_add, map_mul, map_sub, h1, map_one]
  ring

/- English proof (translation)
Establish `h1 : ZMod.castHom h (ZMod d) (idem r N) = 0`. Unfold `idem`. Rewrite using `[map_natCast, ZMod.natCast_eq_zero_iff]`. Conclude with `dvd_pow hd (Nat.totient_pos.2 (pow_pos hr.pos _)).ne'`. Apply `Units.ext` to reduce the goal to its premises.

Use `show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = 1`. Rewrite using `[map_add, map_mul, map_sub, h1, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem projB {N : ℕ} (r d : ℕ) (hr : r.Prime) (h : d ∣ N) (hd : d ∣ ordCompl[r] N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h (proj r N u) = 1 := by
  have h1 : ZMod.castHom h (ZMod d) (idem r N) = 0 := by
    unfold idem
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_pow hd (Nat.totient_pos.2 (pow_pos hr.pos _)).ne'
  apply Units.ext
  show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = 1
  rw [map_add, map_mul, map_sub, h1, map_one]
  ring

/- English proof (translation)
Establish `key : ∀ (d : ℕ) (h : d ∣ N), ZMod.unitsMap h u = ZMod.unitsMap h v → (u : ZMod N).val ≡ (v : ZMod N).val [MOD d]`. Introduce `d h e`. Establish `e' : ZMod.castHom h (ZMod d) (u : ZMod N) = ZMod.castHom h (ZMod d) (v : ZMod N)` using `congrArg Units.val e`. Rewrite `e'` using `[← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N), map_natCast, map_natCast]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).1 e'`.

Establish `h3` using `(Nat.modEq_and_modEq_iff_modEq_mul (coprime_ordProj_ordCompl r N)).1 ⟨key _ _ h1, key _ _ h2⟩`. Rewrite `h3` using `[Nat.ordProj_mul_ordCompl_eq_self]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N)]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).2 h3`.
-/
private theorem crtExt {N : ℕ} [NeZero N] (r : ℕ) {u v : (ZMod N)ˣ}
    (h1 : ZMod.unitsMap (Nat.ordProj_dvd N r) u = ZMod.unitsMap (Nat.ordProj_dvd N r) v)
    (h2 : ZMod.unitsMap (Nat.ordCompl_dvd N r) u = ZMod.unitsMap (Nat.ordCompl_dvd N r) v) : u = v := by
  have key : ∀ (d : ℕ) (h : d ∣ N), ZMod.unitsMap h u = ZMod.unitsMap h v →
      (u : ZMod N).val ≡ (v : ZMod N).val [MOD d] := by
    intro d h e
    have e' : ZMod.castHom h (ZMod d) (u : ZMod N) = ZMod.castHom h (ZMod d) (v : ZMod N) := congrArg Units.val e
    rw [← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N), map_natCast, map_natCast] at e'
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 e'
  have h3 := (Nat.modEq_and_modEq_iff_modEq_mul (coprime_ordProj_ordCompl r N)).1 ⟨key _ _ h1, key _ _ h2⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h3
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

/- English proof (translation)
Establish `hc : d.Coprime (ordProj[r] N)` using `(((Nat.Prime.coprime_iff_not_dvd hr).2 hd).symm).pow_right _`. Apply `hc.dvd_of_dvd_mul_left` to reduce the goal to its premises. Rewrite using `[Nat.ordProj_mul_ordCompl_eq_self]` and apply the resulting hypothesis.
-/
private theorem dvdCompl {N : ℕ} [NeZero N] {r d : ℕ} (hr : r.Prime) (h : d ∣ N) (hd : ¬ r ∣ d) : d ∣ ordCompl[r] N := by
  have hc : d.Coprime (ordProj[r] N) := (((Nat.Prime.coprime_iff_not_dvd hr).2 hd).symm).pow_right _
  apply hc.dvd_of_dvd_mul_left
  rwa [Nat.ordProj_mul_ordCompl_eq_self]

/- English proof (translation)
Rewrite using `[← ZMod.unitsMap_comp h1 h2]`. Both sides reduce to the same expression.
-/
private theorem mapMap {N M d : ℕ} (h1 : d ∣ M) (h2 : M ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← ZMod.unitsMap_comp h1 h2]; rfl

/- English proof (translation)
Introduce `N _ r hr`. Establish `hA` using `projA r _ (Nat.ordProj_dvd N r) dvd_rfl`. Establish `hB` using `projB r _ hr (Nat.ordCompl_dvd N r) dvd_rfl`. Establish `hM : ∀ (r : ℕ), r.Prime → ∀ (M : ℕ) (h : M ∣ N), ¬ r ∣ M → ∀ u, ZMod.unitsMap h (proj r N u) = 1` using `fun r hr M h hM u => projB r M hr h (dvdCompl hr h hM) u`. Use `⟨hA, hB, fun u => crtExt r (hA _) (by rw [hB, hB]), fun r' hr' hne u => ?_, fun hN u => ?_, ?_, ?_, hM r hr, fun M h u => ?_⟩` and prove the remaining obligations.

Use `crtExt r ?_ (by rw [hB, map_one])` and prove the remaining obligations. Rewrite using `[hA, map_one]`. Conclude with `hM r' hr' _ _ (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hr' hr).1 (hr'.dvd_of_dvd_pow hd))) u`. Use `hM r hr N dvd_rfl hN u` as an intermediate fact. Rewrite `this` using `[ZMod.unitsMap_self]`. Then use the resulting hypothesis.

Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`. Conclude with `hB v`. Introduce `hu`.

Conclude with `⟨u, crtExt r (hA u) ((hB u).trans (MonoidHom.mem_ker.1 hu).symm)⟩`. Use extensionality with `u`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`.

Rewrite using `[← hA, hu, map_one]`. Introduce `hu`. Conclude with `crtExt r (by rw [hA, hu, map_one]) (by rw [hB, map_one])`. Use `haveI : NeZero M := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) h⟩`. Use `crtExt r ?_ ?_` and prove the remaining obligations.

Rewrite using `[projA r _ _ dvd_rfl, mapMap, mapMap]`. Conclude with `projA r _ _ (Nat.ordProj_dvd_ordProj_of_dvd (NeZero.ne N) h r) u`. Rewrite using `[projB r _ hr _ dvd_rfl, mapMap]`. Conclude with `projB r _ hr _ (Nat.ordCompl_dvd_ordCompl_of_dvd h r) u`.
-/
theorem UpperTheory.V.HV.projFacts :
    ∀ (N : ℕ) [NeZero N] (r : ℕ), r.Prime →
      (∀ u, ZMod.unitsMap (Nat.ordProj_dvd N r) (proj r N u) = ZMod.unitsMap (Nat.ordProj_dvd N r) u) ∧
      (∀ u, ZMod.unitsMap (Nat.ordCompl_dvd N r) (proj r N u) = 1) ∧ (∀ u, proj r N (proj r N u) = proj r N u) ∧
      (∀ r', r'.Prime → r' ≠ r → ∀ u, proj r N (proj r' N u) = 1) ∧ (¬ r ∣ N → ∀ u, proj r N u = 1) ∧
      (proj r N).range = (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker ∧ (proj r N).ker = (ZMod.unitsMap (Nat.ordProj_dvd N r)).ker ∧
      (∀ (M : ℕ) (h : M ∣ N), ¬ r ∣ M → ∀ u, ZMod.unitsMap h (proj r N u) = 1) ∧
      ∀ (M : ℕ) (h : M ∣ N) u, ZMod.unitsMap h (proj r N u) = proj r M (ZMod.unitsMap h u) := by
  intro N _ r hr
  have hA := projA r _ (Nat.ordProj_dvd N r) dvd_rfl
  have hB := projB r _ hr (Nat.ordCompl_dvd N r) dvd_rfl
  have hM : ∀ (r : ℕ), r.Prime → ∀ (M : ℕ) (h : M ∣ N), ¬ r ∣ M → ∀ u, ZMod.unitsMap h (proj r N u) = 1 :=
    fun r hr M h hM u => projB r M hr h (dvdCompl hr h hM) u
  refine ⟨hA, hB, fun u => crtExt r (hA _) (by rw [hB, hB]), fun r' hr' hne u => ?_, fun hN u => ?_, ?_, ?_,
    hM r hr, fun M h u => ?_⟩
  · refine crtExt r ?_ (by rw [hB, map_one])
    rw [hA, map_one]
    exact hM r' hr' _ _ (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hr' hr).1 (hr'.dvd_of_dvd_pow hd))) u
  · have := hM r hr N dvd_rfl hN u
    rwa [ZMod.unitsMap_self] at this
  · ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact hB v
    · intro hu
      exact ⟨u, crtExt r (hA u) ((hB u).trans (MonoidHom.mem_ker.1 hu).symm)⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hu
      rw [← hA, hu, map_one]
    · intro hu
      exact crtExt r (by rw [hA, hu, map_one]) (by rw [hB, map_one])
  · haveI : NeZero M := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) h⟩
    refine crtExt r ?_ ?_
    · rw [projA r _ _ dvd_rfl, mapMap, mapMap]
      exact projA r _ _ (Nat.ordProj_dvd_ordProj_of_dvd (NeZero.ne N) h r) u
    · rw [projB r _ hr _ dvd_rfl, mapMap]
      exact projB r _ hr _ (Nat.ordCompl_dvd_ordCompl_of_dvd h r) u
