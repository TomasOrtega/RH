import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn⟩`. Establish `hle : χ.range ≤ rootsOfUnity n O`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `(mem_rootsOfUnity _ _).mpr (hχ g)`. Use `haveI : Finite χ.range := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)`.

Take `⟨x, hx⟩` from `IsCyclic.exists_generator (α := χ.range)`. Take `⟨g0, hg0⟩` from `x.2`. Establish `hpow : ∀ g, ∃ k : ℕ, χ g = χ g0 ^ k`. Introduce `g`. Take `⟨k, hk⟩ : (⟨χ g, g, rfl⟩ : χ.range) ∈ Submonoid.powers x` from `mem_powers_iff_mem_zpowers.mpr (hx _)`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `e : ((x ^ k : χ.range) : Oˣ) = χ g` using `congrArg Subtype.val hk`. Rewrite `e` using `[SubmonoidClass.coe_pow, ← hg0]`. Conclude with `e.symm`. Establish `hord : orderOf (χ g0) ≠ 0` using `(orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hχ g0⟩)).ne'`.

Use `haveI : NeZero (orderOf (χ g0)) := ⟨hord⟩`. Establish `hηm : η g0 ∈ rootsOfUnity (orderOf (χ g0)) O`. Rewrite using `[mem_rootsOfUnity, ← map_pow]`. Apply `h` to reduce the goal to its premises. Rewrite using `[map_pow, pow_orderOf_eq_one]`.

Take `⟨j, -, hj⟩` from `(IsPrimitiveRoot.orderOf (χ g0)).eq_pow_of_mem_rootsOfUnity hηm`. Use `⟨j, fun g => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hpow g`. Establish `hker : χ (g * (g0 ^ k)⁻¹) = 1` using `by rw [map_mul, map_inv, map_pow, hk, mul_inv_cancel]`. Establish `hη` using `h _ hker`.

Rewrite `hη` using `[map_mul, map_inv, mul_inv_eq_one, map_pow]`. Rewrite using `[hη, hk, ← hj, ← pow_mul, ← pow_mul, mul_comm]`.
-/
private theorem gdIff_pow {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (χ η : Γ →* Oˣ) {n : ℕ} (hn : n ≠ 0)
    (hχ : ∀ g, χ g ^ n = 1) (h : ∀ g, χ g = 1 → η g = 1) : ∃ j : ℕ, ∀ g, η g = χ g ^ j := by
  classical
  haveI : NeZero n := ⟨hn⟩
  have hle : χ.range ≤ rootsOfUnity n O := by
    rintro _ ⟨g, rfl⟩
    exact (mem_rootsOfUnity _ _).mpr (hχ g)
  haveI : Finite χ.range :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := χ.range)
  obtain ⟨g0, hg0⟩ := x.2
  have hpow : ∀ g, ∃ k : ℕ, χ g = χ g0 ^ k := by
    intro g
    obtain ⟨k, hk⟩ : (⟨χ g, g, rfl⟩ : χ.range) ∈ Submonoid.powers x :=
      mem_powers_iff_mem_zpowers.mpr (hx _)
    refine ⟨k, ?_⟩
    have e : ((x ^ k : χ.range) : Oˣ) = χ g := congrArg Subtype.val hk
    rw [SubmonoidClass.coe_pow, ← hg0] at e
    exact e.symm
  have hord : orderOf (χ g0) ≠ 0 :=
    (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hχ g0⟩)).ne'
  haveI : NeZero (orderOf (χ g0)) := ⟨hord⟩
  have hηm : η g0 ∈ rootsOfUnity (orderOf (χ g0)) O := by
    rw [mem_rootsOfUnity, ← map_pow]
    apply h
    rw [map_pow, pow_orderOf_eq_one]
  obtain ⟨j, -, hj⟩ := (IsPrimitiveRoot.orderOf (χ g0)).eq_pow_of_mem_rootsOfUnity hηm
  refine ⟨j, fun g => ?_⟩
  obtain ⟨k, hk⟩ := hpow g
  have hker : χ (g * (g0 ^ k)⁻¹) = 1 := by rw [map_mul, map_inv, map_pow, hk, mul_inv_cancel]
  have hη := h _ hker
  rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at hη
  rw [hη, hk, ← hj, ← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Establish `hne : (-1 : Oˣ) ≠ 1`. Introduce `h1`. Establish `h2` using `congrArg (fun u : Oˣ => (u : O)) h1`. Simplify using `only [Units.val_neg, Units.val_one] at h2`. Establish `h3 : (2 : O) = 0` using `by linear_combination -h2`.

Conclude with `two_ne_zero h3`. Set `η : Γ →* Oˣ` to `{ toFun := fun g => if g ∈ H then 1 else -1 map_one' := by simp [H.one_mem] map_mul' := by`. Introduce `a b`. Apply the tactic sequence `by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;>`. Simplify using `[ha, hb, Subgroup.mul_mem_iff_of_index_two h] }`.

Use `⟨η, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `g`. Rewrite using `[MonoidHom.mem_ker]`. Distinguish the cases in `hg : g ∈ H`. Simplify using `[η, hg]`.

Simplify using `[η, hg, hne]`. Introduce `g`. Distinguish the cases in `hg : g ∈ H`. Simplify using `[η, hg]`. Simplify using `[η, hg]`.
-/
private theorem gdIff_sign {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [CharZero O] (H : Subgroup Γ) (h : H.index = 2) :
    ∃ η : Γ →* Oˣ, η.ker = H ∧ ∀ g, η g ^ 2 = 1 := by
  classical
  have hne : (-1 : Oˣ) ≠ 1 := by
    intro h1
    have h2 := congrArg (fun u : Oˣ => (u : O)) h1
    simp only [Units.val_neg, Units.val_one] at h2
    have h3 : (2 : O) = 0 := by linear_combination -h2
    exact two_ne_zero h3
  let η : Γ →* Oˣ :=
    { toFun := fun g => if g ∈ H then 1 else -1
      map_one' := by simp [H.one_mem]
      map_mul' := by
        intro a b
        by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;>
          simp [ha, hb, Subgroup.mul_mem_iff_of_index_two h] }
  refine ⟨η, ?_, ?_⟩
  · ext g
    rw [MonoidHom.mem_ker]
    by_cases hg : g ∈ H
    · simp [η, hg]
    · simp [η, hg, hne]
  · intro g
    by_cases hg : g ∈ H
    · simp [η, hg]
    · simp [η, hg]

/- English proof (translation)
Establish `: IsAlgClosure K Ω` using `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`. Conclude with `(galEmbTop ℚ K Ω).2.2`.
-/
private theorem gdIff_index (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] :
    (galOf ℚ K Ω).index = Module.finrank ℚ K := by
  have : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact (galEmbTop ℚ K Ω).2.2

/- English proof (translation)
Introduce `Ω _ _ _ K _ _ _ l _ c e N _ ψ`. Establish `hl : l.Prime` using `Fact.out`. Take `⟨A0, hA0⟩` from `(Chr.placesQ Ω).1 l hl`. Establish `F1 : ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w → (∀ χ1 χ2 : DirichletCharacter c.O N, Chr.dirG ℚ Ω (χ1 * χ2) = Chr.dirG ℚ Ω χ1 * Chr.dirG ℚ Ω χ2) ∧ (∀ χ : DirichletCharacter c.O N, Chr.dirG ℚ Ω χ⁻¹ = (Chr.dirG ℚ Ω χ)⁻¹) ∧ (∀ χ1 χ2 : DirichletCharacter c.O N, Chr.dirG ℚ Ω χ1 = Chr.dirG ℚ Ω χ …`. Introduce `w hw`.

Establish `hm : ∀ χ1 χ2 : DirichletCharacter c.O N, Chr.dirG ℚ Ω (χ1 * χ2) = Chr.dirG ℚ Ω χ1 * Chr.dirG ℚ Ω χ2` using `fun χ1 χ2 => ((psiBar Ω l c w hw N χ1).2.2.2 χ2).1`. Establish `h1 : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1`. Use `hm 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `(mul_left_cancel (a := Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N)) (by rw [mul_one]; exact this)).symm`.

Use `⟨hm, fun χ => ?_, fun χ1 χ2 h => ((psiBar Ω l c w hw N χ1).2.2.2 χ2).2 h, h1⟩` and prove the remaining obligations. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hm, inv_mul_cancel, h1]`. Establish `Uq : ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w → ∀ u v : ℕ, u < l - 1 → v < l - 1 → (∀ σ ∈ Ine A0, w σ ^ u = w σ ^ v) → u = v`. Introduce `w hw`.

Establish `OM` using `(omT Ω l c).2 w hw`. Establish `key : ∀ u v : ℕ, u < l - 1 → v < l - 1 → u ≤ v → (∀ σ ∈ Ine A0, w σ ^ u = w σ ^ v) → u = v`. Introduce `u v hu hv huv h`. Establish `hd : l - 1 ∣ v - u` using `OM.2.2.2.2.2.2.1 A0 hA0 (v - u) (fun σ hσ => by`. Rewrite using `[MonoidHom.mem_ker]`.

Use `show w σ ^ (v - u) = 1`. Use `h σ hσ` as an intermediate fact. Rewrite `this` using `[← Nat.add_sub_cancel' huv, pow_add]`. Conclude with `mul_left_cancel (this.symm.trans (mul_one _).symm))`. Use `Nat.eq_zero_of_dvd_of_lt hd (by omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `u v hu hv h`. Break down `le_total u v with huv | huv` into its components or cases. Conclude with `key u v hu hv huv h`. Conclude with `(key v u hv hu huv (fun σ hσ => (h σ hσ).symm)).symm`.

Establish `TH : ¬ l ∣ orderOf ψ → th0 l ψ = ψ`. Introduce `hord`. Conclude with `((partOrd (DirichletCharacter c.O N) l hl ψ (Nat.pos_of_ne_zero (fun h0 => hord (h0 ▸ dvd_zero l)))).2.2.2.2.2.1 hord).2`. Establish `HC : ∀ (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a → Chr.dirG ℚ Ω (comp l ψ) = w ^ a ∧ Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹ ∧ ¬ l ∣ orderOf ψ`. Introduce `w η a hL`.

Take `⟨hm, hinv, -, -⟩` from `F1 w hL.om`. Establish `hord : ¬ l ∣ orderOf ψ`. Rewrite using `[← (psiBar Ω l c w hL.om N ψ).2.2.1]`. Conclude with `hL.ord`. Establish `hth` using `TH hord`.

Take `⟨b, hb, hcb, -⟩` from `(psiBar Ω l c w hL.om N ψ).1`. Rewrite `hcb` using `[hth]`. Establish `hab : a = b` using `Uq w hL.om a b hL.a_lt hb (fun σ hσ => by`. Establish `e1` using `hL.ine A0 hA0 σ hσ`. Establish `e2` using `((compIne Ω N l hl A0 hA0).2 c.O ψ).1 σ hσ`.

Rewrite `e2` using `[hcb]`. Conclude with `e1.symm.trans e2)`. Substitute `hab` using the available equality. Use `⟨hcb, ?_, hord⟩` and prove the remaining obligations. Unfold `chiP`.

Rewrite using `[hth, hm, hinv, hcb]`. Use `⟨⟨?_, ?_⟩, fun w η a hL => (HC w η a hL).2.1⟩` and prove the remaining obligations. Introduce `hG`. Take `⟨⟨w, hw, -⟩, -⟩` from `omT Ω l c`. Take `⟨hm, hinv, -, h1⟩` from `F1 w hw`.

Establish `OM` using `(omT Ω l c).2 w hw`. Establish `hord` using `hG.ord`. Establish `hth` using `TH hord`. Take `⟨b, hb, hcb, -⟩` from `(psiBar Ω l c w hw N ψ).1`. Rewrite `hcb` using `[hth]`.

Establish `hidx : (galOf ℚ K Ω).index = 2` using `by rw [gdIff_index, hG.quad]`. Take `⟨η, hηk, hη2⟩` from `gdIff_sign (O := c.O) (galOf ℚ K Ω) hidx`. Establish `hχ' : Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ b)⁻¹`. Unfold `chiP`. Rewrite using `[hth, hm, hinv, hcb]`.

Establish `h2b : l - 1 ∣ 2 * b`. Rewrite using `[← OM.2.2.1]`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Establish `: Chr.dirG ℚ Ω (comp l ψ ^ 2) = 1` using `by rw [hG.ine, h1]`. Rewrite `this` using `[pow_two, hm, hcb, ← pow_add, ← two_mul]`.

Conclude with `this`. Use `⟨w, η, b, ⟨hw, hηk, hG.l_odd, hG.e_pos, hG.N_even, ?_, ?_, hb, h2b, ?_, hG.quad, hG.imag, hG.l_cop, hG.cop, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(psiBar Ω l c w hw N ψ).2.2.1]`. Conclude with `hord`. Introduce `A hA σ hσ`.

Express the relevant statement in the definitionally equal form `Chr.dirG ℚ Ω ψ σ = (w ^ b) σ`. Rewrite using `[((compIne Ω N l hl A hA).2 c.O ψ).1 σ hσ, hcb]`. Introduce `σ hσ`. Conclude with `((psiBar Ω l c w hw N ψ).2.1 e).mp hG.par σ hσ`. Introduce `i j hC`.

Apply `hG.eta` to reduce the goal to its premises. Establish `hd1 : Chr.dirG ℚ Ω ψ ^ orderOf ψ = 1`. Rewrite using `[← (psiBar Ω l c w hw N ψ).2.2.1]`. Conclude with `pow_orderOf_eq_one _`. Establish `hwS : w ∈ (powMonoidHom (2 * ((l - 1) * orderOf ψ)) : (G ℚ Ω →* c.Oˣ) →* _).ker`.

Rewrite using `[MonoidHom.mem_ker, powMonoidHom_apply, show 2 * ((l - 1) * orderOf ψ) = (l - 1) * (2 * orderOf ψ) by ring, pow_mul, hw.1, one_pow]`. Establish `hψS : Chr.dirG ℚ Ω ψ ∈ (powMonoidHom (2 * ((l - 1) * orderOf ψ)) : (G ℚ Ω →* c.Oˣ) →* _).ker`. Rewrite using `[MonoidHom.mem_ker, powMonoidHom_apply, show 2 * ((l - 1) * orderOf ψ) = orderOf ψ * (2 * (l - 1)) by ring, pow_mul, hd1, one_pow]`. Establish `hXS` using `Subgroup.mul_mem _ (Subgroup.pow_mem _ hwS i) (Subgroup.pow_mem _ (Subgroup.mul_mem _ hψS (Subgroup.inv_mem _ (Subgroup.pow_mem _ hwS b))) j)`. Rewrite `hXS` using `[MonoidHom.mem_ker, powMonoidHom_apply]`.

Establish `hηm : η ^ (2 * ((l - 1) * orderOf ψ)) = 1`. Use `MonoidHom.ext fun σ => ?_` and prove the remaining obligations. Use `show η σ ^ (2 * ((l - 1) * orderOf ψ)) = 1`. Rewrite using `[pow_mul, hη2, one_pow]`. Establish `hlm : ¬ l ∣ 2 * ((l - 1) * orderOf ψ)`.

Introduce `hdiv`. Break down `(Nat.Prime.dvd_mul hl).mp hdiv with h2 | h'` into its components or cases. Conclude with `hG.l_odd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h2)`. Break down `(Nat.Prime.dvd_mul hl).mp h' with h3 | h4` into its components or cases. Use `hl.two_le` as an intermediate fact.

Use `Nat.le_of_dvd (by omega) h3` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `hord h4`. Establish `heq` using `(congrFacts Ω l c).2.2.2.2 η _ _ hlm hηm hXS hC`. Rewrite using `[← OM.1, hχ', ← hηk, heq]`.

Introduce `σ hσ`. Take `⟨hσ1, hσ2⟩` from `Subgroup.mem_inf.mp hσ`. Rewrite `hσ1`, `hσ2`, the goal using `[MonoidHom.mem_ker]`. Use `show w σ ^ i * ((Chr.dirG ℚ Ω ψ * (w ^ b)⁻¹) σ) ^ j = 1`. Rewrite using `[hσ2, hσ1, one_pow, one_pow, one_mul]`.

Introduce `hd`. Apply `hG.gen` to reduce the goal to its premises. Conclude with `(Nat.dvd_add_right h2b).mp (by rw [show 2 * b + 2 * e = 2 * (e + b) by ring]; exact hd)`. Introduce and unpack `⟨w, η, a, hL⟩`. Take `⟨hm, hinv, hinj, h1⟩` from `F1 w hL.om`.

Establish `OM` using `(omT Ω l c).2 w hL.om`. Take `⟨hcomp, hχ', hord⟩` from `HC w η a hL`. Establish `h2a : w ^ (2 * a) = 1`. Take `⟨k, hk⟩` from `hL.two_a`. Rewrite using `[hk, pow_mul, hL.om.1, one_pow]`.

Use `⟨hL.l_odd, hL.e_pos, hL.N_even, hord, ?_, ?_, hL.quad, hL.imag, hL.l_cop, hL.cop, ?_, ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[pow_two, hm, hcomp, h1, ← pow_add, ← two_mul, h2a]`. Conclude with `((psiBar Ω l c w hL.om N ψ).2.1 e).mpr hL.par`. Introduce `hle`.

Take `⟨χ', hχ'e⟩ : ∃ χ' : G ℚ Ω →* c.Oˣ, χ' = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹` from `⟨_, rfl⟩`. Rewrite `hle` using `[← OM.1, hχ', ← hχ'e]`. Establish `hn : orderOf (Chr.dirG ℚ Ω ψ) * (l - 1) ≠ 0` using `mul_ne_zero (fun h0 => hL.ord (h0 ▸ dvd_zero l)) (by have := hl.two_le; omega)`. Establish `hwS : w ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) : (G ℚ Ω →* c.Oˣ) →* _).ker`. Rewrite using `[MonoidHom.mem_ker, powMonoidHom_apply, mul_comm, pow_mul, hL.om.1, one_pow]`.

Establish `hψS : Chr.dirG ℚ Ω ψ ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) : (G ℚ Ω →* c.Oˣ) →* _).ker`. Rewrite using `[MonoidHom.mem_ker, powMonoidHom_apply, pow_mul, pow_orderOf_eq_one, one_pow]`. Establish `hχS : χ' ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) : (G ℚ Ω →* c.Oˣ) →* _).ker`. Rewrite using `[hχ'e]`. Conclude with `Subgroup.mul_mem _ hψS (Subgroup.inv_mem _ (Subgroup.pow_mem _ hwS a))`.

Rewrite `hχS` using `[MonoidHom.mem_ker, powMonoidHom_apply]`. Establish `hpowχ : ∀ g, (χ'.comp w.ker.subtype) g ^ (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) = 1` using `fun g => congrArg (fun f : G ℚ Ω →* c.Oˣ => f g) hχS`. Establish `hker : ∀ g, (χ'.comp w.ker.subtype) g = 1 → (η.comp w.ker.subtype) g = 1`. Introduce `g hg`. Establish `: (g : G ℚ Ω) ∈ η.ker`.

Rewrite using `[hL.eta_ker]`. Conclude with `hle ⟨g.2, hg⟩`. Conclude with `this`. Take `⟨j, hj⟩` from `gdIff_pow (χ'.comp w.ker.subtype) (η.comp w.ker.subtype) hn hpowχ hker`. Establish `hθ : w.ker ≤ (η * (χ' ^ j)⁻¹).ker`.

Introduce `σ hσ`. Rewrite using `[MonoidHom.mem_ker]`. Use `show η σ * ((χ' σ) ^ j)⁻¹ = 1`. Use `hj ⟨σ, hσ⟩` as an intermediate fact. Rewrite using `[show η σ = χ' σ ^ j from this, mul_inv_cancel]`.

Take `⟨b', -, hb'⟩` from `OM.2.2.2.2.2.2.2 _ hθ`. Apply `hL.eta b' j` to reduce the goal to its premises. Rewrite using `[← hχ'e]`. Establish `heq : η = w ^ b' * χ' ^ j`. Rewrite using `[← hb']`.

Conclude with `(inv_mul_cancel_right η (χ' ^ j)).symm`. Rewrite using `[← heq]`. Conclude with `(congrFacts Ω l c).1.refl _`. Introduce `hd`. Apply `hL.gen` to reduce the goal to its premises.

Rewrite using `[show 2 * (e + a) = 2 * e + 2 * a by ring]`. Conclude with `dvd_add hd hL.two_a`.
-/
theorem UpperTheory.V.HV.gdIff :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e N : ℕ) [NeZero N]
      (ψ : DirichletCharacter c.O N), (GD Ω K l e ψ ↔ ∃ (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a) ∧
        ∀ (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a → Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹ := by
  intro Ω _ _ _ K _ _ _ l _ c e N _ ψ
  have hl : l.Prime := Fact.out
  obtain ⟨A0, hA0⟩ := (Chr.placesQ Ω).1 l hl
  have F1 : ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w →
      (∀ χ1 χ2 : DirichletCharacter c.O N,
        Chr.dirG ℚ Ω (χ1 * χ2) = Chr.dirG ℚ Ω χ1 * Chr.dirG ℚ Ω χ2) ∧
      (∀ χ : DirichletCharacter c.O N, Chr.dirG ℚ Ω χ⁻¹ = (Chr.dirG ℚ Ω χ)⁻¹) ∧
      (∀ χ1 χ2 : DirichletCharacter c.O N, Chr.dirG ℚ Ω χ1 = Chr.dirG ℚ Ω χ2 → χ1 = χ2) ∧
      Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1 := by
    intro w hw
    have hm : ∀ χ1 χ2 : DirichletCharacter c.O N,
        Chr.dirG ℚ Ω (χ1 * χ2) = Chr.dirG ℚ Ω χ1 * Chr.dirG ℚ Ω χ2 :=
      fun χ1 χ2 => ((psiBar Ω l c w hw N χ1).2.2.2 χ2).1
    have h1 : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N) = 1 := by
      have := hm 1 1
      rw [mul_one] at this
      exact (mul_left_cancel (a := Chr.dirG ℚ Ω (1 : DirichletCharacter c.O N))
        (by rw [mul_one]; exact this)).symm
    refine ⟨hm, fun χ => ?_, fun χ1 χ2 h => ((psiBar Ω l c w hw N χ1).2.2.2 χ2).2 h, h1⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← hm, inv_mul_cancel, h1]
  have Uq : ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w → ∀ u v : ℕ, u < l - 1 → v < l - 1 →
      (∀ σ ∈ Ine A0, w σ ^ u = w σ ^ v) → u = v := by
    intro w hw
    have OM := (omT Ω l c).2 w hw
    have key : ∀ u v : ℕ, u < l - 1 → v < l - 1 → u ≤ v →
        (∀ σ ∈ Ine A0, w σ ^ u = w σ ^ v) → u = v := by
      intro u v hu hv huv h
      have hd : l - 1 ∣ v - u := OM.2.2.2.2.2.2.1 A0 hA0 (v - u) (fun σ hσ => by
        rw [MonoidHom.mem_ker]
        show w σ ^ (v - u) = 1
        have := h σ hσ
        rw [← Nat.add_sub_cancel' huv, pow_add] at this
        exact mul_left_cancel (this.symm.trans (mul_one _).symm))
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    intro u v hu hv h
    rcases le_total u v with huv | huv
    · exact key u v hu hv huv h
    · exact (key v u hv hu huv (fun σ hσ => (h σ hσ).symm)).symm
  have TH : ¬ l ∣ orderOf ψ → th0 l ψ = ψ := by
    intro hord
    exact ((partOrd (DirichletCharacter c.O N) l hl ψ
      (Nat.pos_of_ne_zero (fun h0 => hord (h0 ▸ dvd_zero l)))).2.2.2.2.2.1 hord).2
  have HC : ∀ (w η : G ℚ Ω →* c.Oˣ) (a : ℕ), GDlit c K e ψ w η a →
      Chr.dirG ℚ Ω (comp l ψ) = w ^ a ∧
      Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹ ∧ ¬ l ∣ orderOf ψ := by
    intro w η a hL
    obtain ⟨hm, hinv, -, -⟩ := F1 w hL.om
    have hord : ¬ l ∣ orderOf ψ := by
      rw [← (psiBar Ω l c w hL.om N ψ).2.2.1]
      exact hL.ord
    have hth := TH hord
    obtain ⟨b, hb, hcb, -⟩ := (psiBar Ω l c w hL.om N ψ).1
    rw [hth] at hcb
    have hab : a = b := Uq w hL.om a b hL.a_lt hb (fun σ hσ => by
      have e1 := hL.ine A0 hA0 σ hσ
      have e2 := ((compIne Ω N l hl A0 hA0).2 c.O ψ).1 σ hσ
      rw [hcb] at e2
      exact e1.symm.trans e2)
    subst hab
    refine ⟨hcb, ?_, hord⟩
    unfold chiP
    rw [hth, hm, hinv, hcb]
  refine ⟨⟨?_, ?_⟩, fun w η a hL => (HC w η a hL).2.1⟩
  · intro hG
    obtain ⟨⟨w, hw, -⟩, -⟩ := omT Ω l c
    obtain ⟨hm, hinv, -, h1⟩ := F1 w hw
    have OM := (omT Ω l c).2 w hw
    have hord := hG.ord
    have hth := TH hord
    obtain ⟨b, hb, hcb, -⟩ := (psiBar Ω l c w hw N ψ).1
    rw [hth] at hcb
    have hidx : (galOf ℚ K Ω).index = 2 := by rw [gdIff_index, hG.quad]
    obtain ⟨η, hηk, hη2⟩ := gdIff_sign (O := c.O) (galOf ℚ K Ω) hidx
    have hχ' : Chr.dirG ℚ Ω (chiP l ψ) = Chr.dirG ℚ Ω ψ * (w ^ b)⁻¹ := by
      unfold chiP
      rw [hth, hm, hinv, hcb]
    have h2b : l - 1 ∣ 2 * b := by
      rw [← OM.2.2.1]
      apply orderOf_dvd_of_pow_eq_one
      have : Chr.dirG ℚ Ω (comp l ψ ^ 2) = 1 := by rw [hG.ine, h1]
      rw [pow_two, hm, hcb, ← pow_add, ← two_mul] at this
      exact this
    refine ⟨w, η, b, ⟨hw, hηk, hG.l_odd, hG.e_pos, hG.N_even, ?_, ?_, hb, h2b, ?_, hG.quad, hG.imag,
      hG.l_cop, hG.cop, ?_, ?_⟩⟩
    · rw [(psiBar Ω l c w hw N ψ).2.2.1]
      exact hord
    · intro A hA σ hσ
      change Chr.dirG ℚ Ω ψ σ = (w ^ b) σ
      rw [((compIne Ω N l hl A hA).2 c.O ψ).1 σ hσ, hcb]
    · intro σ hσ
      exact ((psiBar Ω l c w hw N ψ).2.1 e).mp hG.par σ hσ
    · intro i j hC
      apply hG.eta
      have hd1 : Chr.dirG ℚ Ω ψ ^ orderOf ψ = 1 := by
        rw [← (psiBar Ω l c w hw N ψ).2.2.1]
        exact pow_orderOf_eq_one _
      have hwS : w ∈ (powMonoidHom (2 * ((l - 1) * orderOf ψ)) : (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply,
          show 2 * ((l - 1) * orderOf ψ) = (l - 1) * (2 * orderOf ψ) by ring, pow_mul, hw.1, one_pow]
      have hψS : Chr.dirG ℚ Ω ψ ∈
          (powMonoidHom (2 * ((l - 1) * orderOf ψ)) : (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply,
          show 2 * ((l - 1) * orderOf ψ) = orderOf ψ * (2 * (l - 1)) by ring, pow_mul, hd1, one_pow]
      have hXS := Subgroup.mul_mem _ (Subgroup.pow_mem _ hwS i)
        (Subgroup.pow_mem _ (Subgroup.mul_mem _ hψS (Subgroup.inv_mem _ (Subgroup.pow_mem _ hwS b))) j)
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hXS
      have hηm : η ^ (2 * ((l - 1) * orderOf ψ)) = 1 := by
        refine MonoidHom.ext fun σ => ?_
        show η σ ^ (2 * ((l - 1) * orderOf ψ)) = 1
        rw [pow_mul, hη2, one_pow]
      have hlm : ¬ l ∣ 2 * ((l - 1) * orderOf ψ) := by
        intro hdiv
        rcases (Nat.Prime.dvd_mul hl).mp hdiv with h2 | h'
        · exact hG.l_odd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h2)
        · rcases (Nat.Prime.dvd_mul hl).mp h' with h3 | h4
          · have := hl.two_le
            have := Nat.le_of_dvd (by omega) h3
            omega
          · exact hord h4
      have heq := (congrFacts Ω l c).2.2.2.2 η _ _ hlm hηm hXS hC
      rw [← OM.1, hχ', ← hηk, heq]
      intro σ hσ
      obtain ⟨hσ1, hσ2⟩ := Subgroup.mem_inf.mp hσ
      rw [MonoidHom.mem_ker] at hσ1 hσ2 ⊢
      show w σ ^ i * ((Chr.dirG ℚ Ω ψ * (w ^ b)⁻¹) σ) ^ j = 1
      rw [hσ2, hσ1, one_pow, one_pow, one_mul]
    · intro hd
      apply hG.gen
      exact (Nat.dvd_add_right h2b).mp (by rw [show 2 * b + 2 * e = 2 * (e + b) by ring]; exact hd)
  · rintro ⟨w, η, a, hL⟩
    obtain ⟨hm, hinv, hinj, h1⟩ := F1 w hL.om
    have OM := (omT Ω l c).2 w hL.om
    obtain ⟨hcomp, hχ', hord⟩ := HC w η a hL
    have h2a : w ^ (2 * a) = 1 := by
      obtain ⟨k, hk⟩ := hL.two_a
      rw [hk, pow_mul, hL.om.1, one_pow]
    refine ⟨hL.l_odd, hL.e_pos, hL.N_even, hord, ?_, ?_, hL.quad, hL.imag, hL.l_cop, hL.cop, ?_, ?_⟩
    · apply hinj
      rw [pow_two, hm, hcomp, h1, ← pow_add, ← two_mul, h2a]
    · exact ((psiBar Ω l c w hL.om N ψ).2.1 e).mpr hL.par
    · intro hle
      obtain ⟨χ', hχ'e⟩ : ∃ χ' : G ℚ Ω →* c.Oˣ, χ' = Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹ := ⟨_, rfl⟩
      rw [← OM.1, hχ', ← hχ'e] at hle
      have hn : orderOf (Chr.dirG ℚ Ω ψ) * (l - 1) ≠ 0 :=
        mul_ne_zero (fun h0 => hL.ord (h0 ▸ dvd_zero l)) (by have := hl.two_le; omega)
      have hwS : w ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) :
          (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply, mul_comm, pow_mul, hL.om.1, one_pow]
      have hψS : Chr.dirG ℚ Ω ψ ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) :
          (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply, pow_mul, pow_orderOf_eq_one, one_pow]
      have hχS : χ' ∈ (powMonoidHom (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) :
          (G ℚ Ω →* c.Oˣ) →* _).ker := by
        rw [hχ'e]
        exact Subgroup.mul_mem _ hψS (Subgroup.inv_mem _ (Subgroup.pow_mem _ hwS a))
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hχS
      have hpowχ : ∀ g, (χ'.comp w.ker.subtype) g ^ (orderOf (Chr.dirG ℚ Ω ψ) * (l - 1)) = 1 :=
        fun g => congrArg (fun f : G ℚ Ω →* c.Oˣ => f g) hχS
      have hker : ∀ g, (χ'.comp w.ker.subtype) g = 1 → (η.comp w.ker.subtype) g = 1 := by
        intro g hg
        have : (g : G ℚ Ω) ∈ η.ker := by
          rw [hL.eta_ker]
          exact hle ⟨g.2, hg⟩
        exact this
      obtain ⟨j, hj⟩ := gdIff_pow (χ'.comp w.ker.subtype) (η.comp w.ker.subtype) hn hpowχ hker
      have hθ : w.ker ≤ (η * (χ' ^ j)⁻¹).ker := by
        intro σ hσ
        rw [MonoidHom.mem_ker]
        show η σ * ((χ' σ) ^ j)⁻¹ = 1
        have := hj ⟨σ, hσ⟩
        rw [show η σ = χ' σ ^ j from this, mul_inv_cancel]
      obtain ⟨b', -, hb'⟩ := OM.2.2.2.2.2.2.2 _ hθ
      apply hL.eta b' j
      rw [← hχ'e]
      have heq : η = w ^ b' * χ' ^ j := by
        rw [← hb']
        exact (inv_mul_cancel_right η (χ' ^ j)).symm
      rw [← heq]
      exact (congrFacts Ω l c).1.refl _
    · intro hd
      apply hL.gen
      rw [show 2 * (e + a) = 2 * e + 2 * a by ring]
      exact dvd_add hd hL.two_a
