import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameCentral
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResBase
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResIndep
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsSemisimpleInducedParam
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsoUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameUniq

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Pure

private def eta {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) : I →* ℂˣ :=
  (θ ^ g ^ (j % (n : ℤ)).toNat).comp R

/- English proof (translation)
Simplify using `[eta, MonoidHom.pow_apply]`.
-/
private theorem eta_apply {I K : Type} [Group I] [Field K] (g n : ℕ) (R : I →* Kˣ) (θ : Kˣ →* ℂˣ) (j : ℤ) (t : I) :
    eta g n R θ j t = θ (R t) ^ g ^ (j % (n : ℤ)).toNat := by
  simp [eta, MonoidHom.pow_apply]

end Pure

section Scalars

end Scalars

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz`. Use `haveI : CharZero (HeightOneSpectrum.adicCompletion E w) := (RingHom.charZero_iff (ϕ := i.toRingHom) i.injective).1 inferInstance`. Take `⟨n, c⟩` from `y`. Establish `hcls : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL _)`. Simplify using `[GlobalTheory.LocLanglands.cls, IrrCl.cl_rep]`.

Take `⟨⟨ω, -, hω, hωu⟩, -, -, hpos, -⟩` from `clBasic _ (⟨n, c⟩ : IrrGL _)`. Establish `hn : 0 < n` using `hpos hy`. Take `⟨φ, hφ⟩` from `deg_surjective (h := h) 1`. Rewrite `hy`, `hdz` using `[← hcls]`. Take `⟨hτc, hτu⟩` from `typeEx E Ω A w h g i hi n hn c.rep`.

Take `⟨τ, hτ, hτi⟩` from `hτc hy hdz`. Take `⟨D⟩` from `extEx E Ω A w h g i hi n hn`. Take `⟨⟨R, hR⟩, hRs⟩` from `resEx E Ω A w h g i hi n hn D`. Establish `hT` using `hRs R hR`. Establish `hrank` using `hT.rank`.

Use `haveI : Module.Finite (ZMod g) D.K := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Finite D.K := Module.finite_of_finite (ZMod g)`. Use `letI : Fintype D.K := Fintype.ofFinite _`. Establish `hcard : Fintype.card D.K = g ^ n`. Rewrite using `[Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hrank]`.

Establish `hfix : ∀ x : D.Kˣ, x ^ g ^ n = x` using `fun x => Units.ext (by`. Rewrite using `[Units.val_pow_eq_pow_val, ← hcard, FiniteField.pow_card])`. Establish `hper : ∀ (x : D.Kˣ) (q r : ℕ), x ^ g ^ (n * q + r) = x ^ g ^ r`. Introduce `x q r`. Proceed by induction on `q with`.

Consider the case `zero => simp`. Consider the case `succ q ih => rw [show n * (q + 1) + r = n + (n * q + r) by ring, pow_add, pow_mul, hfix, ih]`. Establish `hmod : ∀ (x : D.Kˣ) (m : ℕ), x ^ g ^ m = x ^ g ^ (m % n)`. Introduce `x m`. Use `conv_lhs => rw [← Nat.div_add_mod m n]`.

Conclude with `hper x _ _`. Establish `hcong : ∀ (x : D.Kˣ) (p q : ℕ), (p : ℤ) ≡ q [ZMOD n] → x ^ g ^ p = x ^ g ^ q`. Introduce `x p q hpq`. Establish `h1 : ((p % n : ℕ) : ℤ) = ((q % n : ℕ) : ℤ)` using `by push_cast; exact hpq`. Rewrite using `[hmod x p, hmod x q, (by exact_mod_cast h1 : p % n = q % n)]`.

Take `⟨hNex, hNuniq, -, hNtr⟩` from `nameLaws g n hn D.K hrank`. Take `⟨θ, hθr, hθN⟩` from `hNex τ hτ`. Establish `hnz : (0 : ℤ) < n` using `by exact_mod_cast hn`. Establish `hex : ∀ j : ℤ, (((j % (n : ℤ)).toNat : ℕ) : ℤ) = j % n` using `fun j => Int.toNat_of_nonneg (Int.emod_nonneg _ hnz.ne')`. Establish `hexlt : ∀ j : ℤ, (j % (n : ℤ)).toNat < n`.

Introduce `j`. Establish `h1` using `hex j`. Establish `h2` using `Int.emod_lt_of_pos j hnz`. Use linear arithmetic over natural numbers and integers. Establish `heta : ∀ (j : ℤ) (t : ↥(Ine A)), eta g n R θ j t = θ (R t ^ g ^ (j % (n : ℤ)).toNat)`.

Introduce `j t`. Rewrite using `[eta_apply, map_pow]`. Establish `hopen : IsOpen (SetLike.coe (eta g n R θ 0).ker)`. Use `Subgroup.isOpen_mono ?_ hT.isOpen` and prove the remaining obligations. Introduce `t ht`.

Rewrite `ht`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[heta, ht, one_pow, map_one]`. Establish `hshift : ∀ (j : ℤ) (t t' : ↥(Ine A)), (ineIncl h) t' = φ * (ineIncl h) t * φ⁻¹ → eta g n R θ j t' = eta g n R θ (j + 1) t`. Introduce `j t t' ht`. Rewrite using `[heta, heta, hT.frob φ t t' hφ ht, ← pow_mul, ← pow_succ']`.

Use `congr 1`. Apply `hcong` to reduce the goal to its premises. Move the coercions through the operations in `[hex]`. Conclude with `((Int.mod_modEq j n).add_right 1).trans (Int.mod_modEq (j + 1) n).symm`. Establish `hinj : ∀ j j' : ℤ, eta g n R θ j = eta g n R θ j' ↔ (n : ℤ) ∣ j - j'`.

Introduce `j j'`. Prove the components needed by the constructor for the conclusion. Introduce `he`. Establish `h1 : θ ^ g ^ (j % (n : ℤ)).toNat = θ ^ g ^ (j' % (n : ℤ)).toNat`. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations.

Take `⟨t, rfl⟩` from `hT.surj x`. Use `congrArg (fun f => f t) he` as an intermediate fact. Simplify `this` using `[eta_apply, MonoidHom.pow_apply]`. Establish `h2` using `hθr _ _ (hexlt j) (hexlt j') h1`. Establish `h3 : j % (n : ℤ) = j' % n` using `by rw [← hex j, ← hex j', h2]`.

Conclude with `Int.ModEq.dvd (show j' ≡ j [ZMOD n] from h3.symm)`. Introduce `hd`. Establish `h3 : j % (n : ℤ) = j' % n` using `(Int.modEq_iff_dvd.mpr hd).symm`. Simplify using `only [eta, h3]`. Take `⟨V, hVirr, hVdim, hVφ, hVine, hVtame⟩` from `indEx E Ω A w h φ hφ n hn (eta g n R θ) hopen hshift hinj (ω (a φ) : ℂ) (Units.ne_zero _)`.

Establish `hInFor : InFor g n R θ V`. Introduce `t`. Rewrite using `[hVine t]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j hj`.

Rewrite `hj` using `[Finset.mem_range]`. Establish `h1 : ((j : ℤ) % (n : ℤ)) = j` using `Int.emod_eq_of_lt (by omega) (by omega)`. Rewrite using `[heta, h1, Int.toNat_natCast]`. Take `⟨⟨δ, hδ⟩, hδu, -, hirr, -, -, -, hm, -⟩` from `wDBasic E Ω A w h V`. Use `⟨V, hVirr, hVdim, hVtame ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `j t ht`. Rewrite using `[heta, hT.wild t ht, one_pow, map_one]`. Introduce `ω' hω' σ'`. Rewrite using `[hωu ω' hω']`. Establish `hNC` using `nameCentral g n hn D.K hrank τ θ hτ hθr hθN`.

Take `⟨ψ, hψ0, hψ⟩` from `hτi`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hψ0 (LinearMap.ext hcon)`.

Establish `hcent : ∀ t : ↥(Ine A), θ (∏ j ∈ Finset.range n, R t ^ g ^ j) = ω (a (ineIncl h t))`. Introduce `t`. Take `⟨u, hu1, hu2⟩` from `resBase E Ω A w h a ha g i hi n hn D R hR t`. Establish `key` using `hψ (GeneralLinearGroup.scalar (Fin n) u) v`. Establish `hred : GlobalTheory.GLp.red g n (GeneralLinearGroup.scalar (Fin n) u) = GeneralLinearGroup.scalar (Fin n) (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u)`.

Use extensionality with `p q`. Apply the tactic sequence `by_cases hpq : p = q <;> simp [GlobalTheory.GLp.red, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq]`. Use `set z : (HeightOneSpectrum.adicCompletion E w)ˣ := Units.map (i.toRingHom.comp PadicInt.Coe.ringHom).toMonoidHom u with hz`. Establish `hinc : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n (GeneralLinearGroup.scalar (Fin n) u)) = GeneralLinearGroup.scalar (Fin n) z`. Use extensionality with `p q`.

Apply the tactic sequence `by_cases hpq : p = q <;> simp [GlobalTheory.GLp.inc, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq, z] <;> rfl`. Rewrite `key` using `[hred, MonoidHom.comp_apply, hinc, hNC, map_smul]`. Rewrite `key` using `[hω z (ψ v)]`. Establish `heq` using `smul_left_injective ℂ hv key`. Apply the tactic sequence `have hzeq : a (ineIncl h t) = z := Units.ext (by rw [hu1]; simp [z] <;> rfl)`.

Establish `hpeq : ∏ j ∈ Finset.range n, R t ^ g ^ j = Units.map (algebraMap (ZMod g) D.K : ZMod g →* D.K) (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u)` using `Units.ext (by simp [hu2])`. Rewrite using `[hzeq, hpeq]`. Conclude with `Units.ext heq`. Establish `hδeq : δ = ω.comp a`. Apply `hδu φ δ (ω.comp a) hφ` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← hδ, hVφ]`. Both sides reduce to the same expression. Introduce `t`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[← hδ, MonoidHom.comp_apply, ← hcent, map_prod]`. Establish `hpol : V.inePol ↑t = (Multiset.map (fun z => X - C z) (do let b ← Multiset.map (fun j => θ (R t ^ g ^ j)) (Multiset.range n); pure (b : ℂ))).prod`. Rewrite using `[hInFor t]`. Simplify using `[Finset.prod_eq_multiset_prod, Multiset.map_map]`. Rewrite using `[(hm t _ hpol).1]`.

Simplify using `[Finset.prod_eq_multiset_prod]`. Rewrite using `[hδ σ', hδeq]`. Both sides reduce to the same expression. Introduce `g' _ i' hi' n' hn' D' R' hR' θ' hθ'r τ' hτ' hN' σ' hσ' hinfl'`. Take `⟨hgg, hii⟩` from `isoUniq _ g g' i i' hi hi'`.

Substitute `g'` using the available equality. Establish `hi2 : i' = i` using `hii i' hi'`. Substitute `i'` using the available equality. Establish `hnn : n' = n` using `congrArg Sigma.fst hσ'`. Substitute `n'` using the available equality.

Establish `hchar` using `hτu σ' τ τ' (hσ'.trans hcls.symm) hτ hτ' hτi hinfl'`. Establish `hNτ : Names g n θ' τ`. Simplify `hN'` using `only [Names, hchar]`. Take `⟨e, he⟩` from `resIndep E Ω A w h g i hi n hn D D' R R' hR hR'`. Take `⟨hN2, hr2⟩` from `hNtr D'.K e τ θ'`.

Take `⟨j, -, hj⟩` from `hNuniq τ θ _ hθr (hr2 hθ'r) hθN (hN2 hNτ)`. Establish `hI` using `(tameUniq E Ω A w h g n D.K R hT θ hθr V hInFor).1 j`. Rewrite `hI` using `[← hj]`. Use `⟨(hirr hVirr).1, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[hI t]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `k _`. Use `congr 3`. Simplify using `only [MonoidHom.comp_apply]`. Use `congr 1`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[he t]`.
-/
theorem parEx : ParEx := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz
  haveI : CharZero (HeightOneSpectrum.adicCompletion E w) :=
    (RingHom.charZero_iff (ϕ := i.toRingHom) i.injective).1 inferInstance
  obtain ⟨n, c⟩ := y
  have hcls : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL _) := by
    simp [GlobalTheory.LocLanglands.cls, IrrCl.cl_rep]
  obtain ⟨⟨ω, -, hω, hωu⟩, -, -, hpos, -⟩ := clBasic _ (⟨n, c⟩ : IrrGL _)
  have hn : 0 < n := hpos hy
  obtain ⟨φ, hφ⟩ := deg_surjective (h := h) 1
  rw [← hcls] at hy hdz
  obtain ⟨hτc, hτu⟩ := typeEx E Ω A w h g i hi n hn c.rep
  obtain ⟨τ, hτ, hτi⟩ := hτc hy hdz
  obtain ⟨D⟩ := extEx E Ω A w h g i hi n hn
  obtain ⟨⟨R, hR⟩, hRs⟩ := resEx E Ω A w h g i hi n hn D
  have hT := hRs R hR
  have hrank := hT.rank
  haveI : Module.Finite (ZMod g) D.K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite D.K := Module.finite_of_finite (ZMod g)
  letI : Fintype D.K := Fintype.ofFinite _
  have hcard : Fintype.card D.K = g ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hrank]
  have hfix : ∀ x : D.Kˣ, x ^ g ^ n = x := fun x => Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← hcard, FiniteField.pow_card])
  have hper : ∀ (x : D.Kˣ) (q r : ℕ), x ^ g ^ (n * q + r) = x ^ g ^ r := by
    intro x q r
    induction q with
    | zero => simp
    | succ q ih => rw [show n * (q + 1) + r = n + (n * q + r) by ring, pow_add, pow_mul, hfix, ih]
  have hmod : ∀ (x : D.Kˣ) (m : ℕ), x ^ g ^ m = x ^ g ^ (m % n) := by
    intro x m
    conv_lhs => rw [← Nat.div_add_mod m n]
    exact hper x _ _
  have hcong : ∀ (x : D.Kˣ) (p q : ℕ), (p : ℤ) ≡ q [ZMOD n] → x ^ g ^ p = x ^ g ^ q := by
    intro x p q hpq
    have h1 : ((p % n : ℕ) : ℤ) = ((q % n : ℕ) : ℤ) := by push_cast; exact hpq
    rw [hmod x p, hmod x q, (by exact_mod_cast h1 : p % n = q % n)]
  obtain ⟨hNex, hNuniq, -, hNtr⟩ := nameLaws g n hn D.K hrank
  obtain ⟨θ, hθr, hθN⟩ := hNex τ hτ
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hex : ∀ j : ℤ, (((j % (n : ℤ)).toNat : ℕ) : ℤ) = j % n := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hnz.ne')
  have hexlt : ∀ j : ℤ, (j % (n : ℤ)).toNat < n := by
    intro j
    have h1 := hex j
    have h2 := Int.emod_lt_of_pos j hnz
    omega
  have heta : ∀ (j : ℤ) (t : ↥(Ine A)), eta g n R θ j t = θ (R t ^ g ^ (j % (n : ℤ)).toNat) := by
    intro j t
    rw [eta_apply, map_pow]
  have hopen : IsOpen (SetLike.coe (eta g n R θ 0).ker) := by
    refine Subgroup.isOpen_mono ?_ hT.isOpen
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    rw [heta, ht, one_pow, map_one]
  have hshift : ∀ (j : ℤ) (t t' : ↥(Ine A)), (ineIncl h) t' = φ * (ineIncl h) t * φ⁻¹ →
      eta g n R θ j t' = eta g n R θ (j + 1) t := by
    intro j t t' ht
    rw [heta, heta, hT.frob φ t t' hφ ht, ← pow_mul, ← pow_succ']
    congr 1
    apply hcong
    push_cast [hex]
    exact ((Int.mod_modEq j n).add_right 1).trans (Int.mod_modEq (j + 1) n).symm
  have hinj : ∀ j j' : ℤ, eta g n R θ j = eta g n R θ j' ↔ (n : ℤ) ∣ j - j' := by
    intro j j'
    constructor
    · intro he
      have h1 : θ ^ g ^ (j % (n : ℤ)).toNat = θ ^ g ^ (j' % (n : ℤ)).toNat := by
        refine MonoidHom.ext fun x => ?_
        obtain ⟨t, rfl⟩ := hT.surj x
        have := congrArg (fun f => f t) he
        simpa [eta_apply, MonoidHom.pow_apply] using this
      have h2 := hθr _ _ (hexlt j) (hexlt j') h1
      have h3 : j % (n : ℤ) = j' % n := by rw [← hex j, ← hex j', h2]
      exact Int.ModEq.dvd (show j' ≡ j [ZMOD n] from h3.symm)
    · intro hd
      have h3 : j % (n : ℤ) = j' % n := (Int.modEq_iff_dvd.mpr hd).symm
      simp only [eta, h3]
  obtain ⟨V, hVirr, hVdim, hVφ, hVine, hVtame⟩ := indEx E Ω A w h φ hφ n hn (eta g n R θ) hopen
    hshift hinj (ω (a φ) : ℂ) (Units.ne_zero _)
  have hInFor : InFor g n R θ V := by
    intro t
    rw [hVine t]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : ((j : ℤ) % (n : ℤ)) = j := Int.emod_eq_of_lt (by omega) (by omega)
    rw [heta, h1, Int.toNat_natCast]
  obtain ⟨⟨δ, hδ⟩, hδu, -, hirr, -, -, -, hm, -⟩ := wDBasic E Ω A w h V
  refine ⟨V, hVirr, hVdim, hVtame ?_, ?_, ?_⟩
  · intro j t ht
    rw [heta, hT.wild t ht, one_pow, map_one]
  · intro ω' hω' σ'
    rw [hωu ω' hω']
    have hNC := nameCentral g n hn D.K hrank τ θ hτ hθr hθN
    obtain ⟨ψ, hψ0, hψ⟩ := hτi
    obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hψ0 (LinearMap.ext hcon)
    have hcent : ∀ t : ↥(Ine A), θ (∏ j ∈ Finset.range n, R t ^ g ^ j) = ω (a (ineIncl h t)) := by
      intro t
      obtain ⟨u, hu1, hu2⟩ := resBase E Ω A w h a ha g i hi n hn D R hR t
      have key := hψ (GeneralLinearGroup.scalar (Fin n) u) v
      have hred : GlobalTheory.GLp.red g n (GeneralLinearGroup.scalar (Fin n) u) =
          GeneralLinearGroup.scalar (Fin n) (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.red, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq]
      set z : (HeightOneSpectrum.adicCompletion E w)ˣ :=
        Units.map (i.toRingHom.comp PadicInt.Coe.ringHom).toMonoidHom u with hz
      have hinc : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n (GeneralLinearGroup.scalar (Fin n) u)) =
          GeneralLinearGroup.scalar (Fin n) z := by
        ext p q
        by_cases hpq : p = q <;> simp [GlobalTheory.GLp.inc, GeneralLinearGroup.scalar, Matrix.diagonal_apply, hpq, z] <;> rfl
      rw [hred, MonoidHom.comp_apply, hinc, hNC, map_smul] at key
      rw [hω z (ψ v)] at key
      have heq := smul_left_injective ℂ hv key
      have hzeq : a (ineIncl h t) = z := Units.ext (by rw [hu1]; simp [z] <;> rfl)
      have hpeq : ∏ j ∈ Finset.range n, R t ^ g ^ j = Units.map (algebraMap (ZMod g) D.K : ZMod g →* D.K)
          (Units.map (PadicInt.toZMod : ℤ_[g] →+* ZMod g).toMonoidHom u) := Units.ext (by simp [hu2])
      rw [hzeq, hpeq]
      exact Units.ext heq
    have hδeq : δ = ω.comp a := by
      apply hδu φ δ (ω.comp a) hφ
      · apply Units.ext
        rw [← hδ, hVφ]
        rfl
      · intro t
        apply Units.ext
        rw [← hδ, MonoidHom.comp_apply, ← hcent, map_prod]
        have hpol : V.inePol ↑t = (Multiset.map (fun z => X - C z)
            (do let b ← Multiset.map (fun j => θ (R t ^ g ^ j)) (Multiset.range n); pure (b : ℂ))).prod := by
          rw [hInFor t]
          simp [Finset.prod_eq_multiset_prod, Multiset.map_map]
        rw [(hm t _ hpol).1]
        simp [Finset.prod_eq_multiset_prod]
    rw [hδ σ', hδeq]
    rfl
  · intro g' _ i' hi' n' hn' D' R' hR' θ' hθ'r τ' hτ' hN' σ' hσ' hinfl'
    obtain ⟨hgg, hii⟩ := isoUniq _ g g' i i' hi hi'
    subst g'
    have hi2 : i' = i := hii i' hi'
    subst i'
    have hnn : n' = n := congrArg Sigma.fst hσ'
    subst n'
    have hchar := hτu σ' τ τ' (hσ'.trans hcls.symm) hτ hτ' hτi hinfl'
    have hNτ : Names g n θ' τ := by
      simpa only [Names, hchar] using hN'
    obtain ⟨e, he⟩ := resIndep E Ω A w h g i hi n hn D D' R R' hR hR'
    obtain ⟨hN2, hr2⟩ := hNtr D'.K e τ θ'
    obtain ⟨j, -, hj⟩ := hNuniq τ θ _ hθr (hr2 hθ'r) hθN (hN2 hNτ)
    have hI := (tameUniq E Ω A w h g n D.K R hT θ hθr V hInFor).1 j
    rw [← hj] at hI
    refine ⟨(hirr hVirr).1, fun t => ?_⟩
    rw [hI t]
    apply Finset.prod_congr rfl
    intro k _
    congr 3
    simp only [MonoidHom.comp_apply]
    congr 1
    apply Units.ext
    simp [he t]

end UpperTheory.Zero.LLC

end
