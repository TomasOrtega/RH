import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

universe u v

section general

variable {R S : Type*} [CommRing R] [CommRing S]

/- English proof (translation)
Unfold `Ring.ord`. Use `haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e`. Use `haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _`. Set `q` to `Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e (by rw [Ideal.map_span, Set.image_singleton]; rfl)`. Set `g : (R ⧸ Ideal.span {x}) ≃ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x})` to `{ q.toAddEquiv with map_smul' := fun r m => by`.

Take `⟨m', rfl⟩` from `Ideal.Quotient.mk_surjective m`. Simplify using `only [AddEquiv.toFun_eq_coe, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv]`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, ← map_mul]`. Use `show q (Ideal.Quotient.mk _ (r * m')) = Ideal.Quotient.mk _ (e r) * q (Ideal.Quotient.mk _ m')`. Simplify using `[q] }`.

Establish `iso : Submodule R (R ⧸ Ideal.span {x}) ≃o Submodule S (S ⧸ Ideal.span {e x})` using `Submodule.orderIsoMapComap g`. Establish `h : Order.krullDim (Submodule R (R ⧸ Ideal.span {x})) = Order.krullDim (Submodule S (S ⧸ Ideal.span {e x}))` using `by first`. Consider the case `exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono) (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)`. Consider the case `exact Order.krullDim_eq_of_orderIso iso`. Unfold `Module.length`.

Use `first`. Consider the case `simp only [h]`. Consider the case `congr 1`.
-/
theorem ord_ringEquiv (e : R ≃+* S) (x : R) : Ring.ord R x = Ring.ord S (e x) := by
  unfold Ring.ord
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _
  let q := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  let g : (R ⧸ Ideal.span {x}) ≃ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) :=
    { q.toAddEquiv with
      map_smul' := fun r m => by
        obtain ⟨m', rfl⟩ := Ideal.Quotient.mk_surjective m
        simp only [AddEquiv.toFun_eq_coe, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv]
        rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq,
          ← map_mul]
        show q (Ideal.Quotient.mk _ (r * m')) = Ideal.Quotient.mk _ (e r) * q (Ideal.Quotient.mk _ m')
        simp [q] }
  have iso : Submodule R (R ⧸ Ideal.span {x}) ≃o Submodule S (S ⧸ Ideal.span {e x}) :=
    Submodule.orderIsoMapComap g
  have h : Order.krullDim (Submodule R (R ⧸ Ideal.span {x})) =
      Order.krullDim (Submodule S (S ⧸ Ideal.span {e x})) := by
    first
      | exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
          (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
      | exact Order.krullDim_eq_of_orderIso iso
  unfold Module.length
  first
    | simp only [h]
    | congr 1

/- English proof (translation)
Use `haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e`. Use `haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _`. Establish `iso : Submodule R R ≃o Submodule S S` using `Submodule.orderIsoMapComap e.toSemilinearEquiv`. Establish `h : Order.krullDim (Submodule R R) = Order.krullDim (Submodule S S)` using `by first`. Consider the case `exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono) (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)`.

Consider the case `exact Order.krullDim_eq_of_orderIso iso`. Consider the case `exact iso.krullDim_eq`. Unfold `Module.length`. Use `first`. Consider the case `simp only [h]`.

Consider the case `congr 1`.
-/
theorem length_self_ringEquiv (e : R ≃+* S) : Module.length R R = Module.length S S := by
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _
  have iso : Submodule R R ≃o Submodule S S := Submodule.orderIsoMapComap e.toSemilinearEquiv
  have h : Order.krullDim (Submodule R R) = Order.krullDim (Submodule S S) := by
    first
      | exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
          (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
      | exact Order.krullDim_eq_of_orderIso iso
      | exact iso.krullDim_eq
  unfold Module.length
  first
    | simp only [h]
    | congr 1

end general

section quot

variable {A : Type u} [CommRing A]

noncomputable def quotQuotComapEquiv (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    (A ⧸ Ideal.span {a}) ⧸ P.asIdeal ≃+*
      A ⧸ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal :=
  have hle : Ideal.span {a} ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal := by
    intro x hx
    show Ideal.Quotient.mk _ x ∈ P.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.asIdeal.zero_mem
  have hP : P.asIdeal = (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal.map
      (Ideal.Quotient.mk (Ideal.span {a})) :=
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  (Ideal.quotEquivOfEq hP).trans (DoubleQuot.quotQuotEquivQuotOfLE hle)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [quotQuotComapEquiv]`. Consider the case `fail`.
-/
theorem quotQuotComapEquiv_mk (a b : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    quotQuotComapEquiv a P (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ b)) =
      Ideal.Quotient.mk _ b := by
  first
    | rfl
    | simp [quotQuotComapEquiv]
    | fail

end quot

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

/- English proof (translation)
Establish `hs : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p`. Use extensionality with `q`. Simplify using `only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_Ici]`. Both sides reduce to the same expression. Establish `hdim : ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞)`.

Rewrite using `[ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici, hs]`. Establish `hsum : Order.height p + Order.coheight p ≤ 2`. Establish `h` using `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum A)`. Establish `h2' : Order.krullDim (PrimeSpectrum A) = 2` using `h2`. Rewrite `h` using `[h2']`.

Establish `h3 : (⨆ q : PrimeSpectrum A, Order.height q + Order.coheight q) = 2`. Establish `h'` using `h.symm`. Rewrite `h'` using `[show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl]`. Conclude with `WithBot.coe_injective h'`. Rewrite using `[← h3]`.

Conclude with `le_iSup (fun q : PrimeSpectrum A => Order.height q + Order.coheight q) p`. Establish `h1 : 1 ≤ Order.height p`. Establish `hb : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) < p` using `by show (⊥ : Ideal A) < p.asIdeal`. Conclude with `bot_lt_iff_ne_bot.mpr (fun h => ha (Ideal.mem_bot.mp (h ▸ hap)))`. Conclude with `le_trans le_add_self (Order.height_add_one_le hb)`.

Establish `hm : Order.height (IsLocalRing.closedPoint A) = 2`. Rewrite using `[← PrimeSpectrum.height_eq_orderHeight]`. Use `show (IsLocalRing.maximalIdeal A).height = 2`. Use `(IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).trans h2` as an intermediate fact. Rewrite `this` using `[show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl]`.

Conclude with `WithBot.coe_injective this`. Establish `hpm : Order.height p = 2 ∨ 1 ≤ Order.coheight p`. Distinguish the cases in `hp : p = IsLocalRing.closedPoint A`. Use `left`. Rewrite using `[hp]`.

Conclude with `hm`. Use `right`. Establish `hle : p ≤ IsLocalRing.closedPoint A` using `by show p.asIdeal ≤ IsLocalRing.maximalIdeal A`. Conclude with `IsLocalRing.le_maximalIdeal p.isPrime.ne_top`. Conclude with `le_trans le_add_self (Order.coheight_add_one_le (lt_of_le_of_ne hle hp))`.

Rewrite using `[PrimeSpectrum.height_eq_orderHeight, hdim]`. Use `clear hm hdim hs`. Generalize the expression as in `Order.height p = h at *`. Generalize the expression as in `Order.coheight p = c at *`. Establish `hc : c ≠ ⊤` using `by rintro rfl; simp at hsum`.

Establish `hh : h ≠ ⊤` using `by rintro rfl; simp at hsum`. Use `lift c to ℕ using hc`. Use `lift h to ℕ using hh`. Normalize the coercions in `at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem height_one_iff_dim_one (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (p : PrimeSpectrum A)
    (hap : a ∈ p.asIdeal) : p.asIdeal.height = 1 ↔ ringKrullDim (A ⧸ p.asIdeal) = 1 := by
  have hs : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_Ici]
    rfl
  have hdim : ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici, hs]
  have hsum : Order.height p + Order.coheight p ≤ 2 := by
    have h := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum A)
    have h2' : Order.krullDim (PrimeSpectrum A) = 2 := h2
    rw [h2'] at h
    have h3 : (⨆ q : PrimeSpectrum A, Order.height q + Order.coheight q) = 2 := by
      have h' := h.symm
      rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at h'
      exact WithBot.coe_injective h'
    rw [← h3]
    exact le_iSup (fun q : PrimeSpectrum A => Order.height q + Order.coheight q) p
  have h1 : 1 ≤ Order.height p := by
    have hb : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) < p := by
      show (⊥ : Ideal A) < p.asIdeal
      exact bot_lt_iff_ne_bot.mpr (fun h => ha (Ideal.mem_bot.mp (h ▸ hap)))
    exact le_trans le_add_self (Order.height_add_one_le hb)
  have hm : Order.height (IsLocalRing.closedPoint A) = 2 := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
    show (IsLocalRing.maximalIdeal A).height = 2
    have := (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).trans h2
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at this
    exact WithBot.coe_injective this
  have hpm : Order.height p = 2 ∨ 1 ≤ Order.coheight p := by
    by_cases hp : p = IsLocalRing.closedPoint A
    · left; rw [hp]; exact hm
    · right
      have hle : p ≤ IsLocalRing.closedPoint A := by
        show p.asIdeal ≤ IsLocalRing.maximalIdeal A
        exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
      exact le_trans le_add_self (Order.coheight_add_one_le (lt_of_le_of_ne hle hp))
  rw [PrimeSpectrum.height_eq_orderHeight, hdim]
  clear hm hdim hs
  generalize Order.height p = h at *
  generalize Order.coheight p = c at *
  have hc : c ≠ ⊤ := by rintro rfl; simp at hsum
  have hh : h ≠ ⊤ := by rintro rfl; simp at hsum
  lift c to ℕ using hc
  lift h to ℕ using hh
  norm_cast at *
  omega

/- English proof (translation)
Use `first`. Consider the case `exact ringKrullDim_eq_of_ringEquiv (quotQuotComapEquiv a P)`. Consider the case `exact (quotQuotComapEquiv a P).ringKrullDim`. Consider the case `exact RingEquiv.ringKrullDim (quotQuotComapEquiv a P)`.
-/
theorem dim_quot_comap (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) =
      ringKrullDim (A ⧸ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal) := by
  first
    | exact ringKrullDim_eq_of_ringEquiv (quotQuotComapEquiv a P)
    | exact (quotQuotComapEquiv a P).ringKrullDim
    | exact RingEquiv.ringKrullDim (quotQuotComapEquiv a P)

/- English proof (translation)
Establish `hM : Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {a}) (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal.primeCompl = P.asIdeal.primeCompl`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`.

Introduce `hx`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `⟨y, hx, rfl⟩`. Establish `hloc : IsLocalization P.asIdeal.primeCompl (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal ⧸ (Ideal.span {a}).map (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal)))` using `hM ▸ inferInstance`. Set `e` to `IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal) (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal ⧸ (Ideal.span {a}).map (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span …`.

Set `f` to `(IsLocalizedModule.linearEquiv P.asIdeal.primeCompl (LocalizedModule.mkLinearMap P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) (Algebra.linearMap (A ⧸ Ideal.span {a}) (Localization.AtPrime P.asIdeal))).extendScalarsOfIsLocalization P.asIdeal.primeCompl (Localization.AtPrime P.asIdea …`. Rewrite using `[f.length_eq, length_self_ringEquiv e.toRingEquiv, ← Module.length_eq_of_surjective Ideal.Quotient.mk_surjective, ordLoc, Ring.ord, Ideal.map_span, Set.image_singleton]`.
-/
theorem length_loc_quot (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    length (Localization.AtPrime P.asIdeal)
        (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P) a := by
  have hM : Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {a})
      (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal.primeCompl =
      P.asIdeal.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨y, hx, rfl⟩
  have hloc : IsLocalization P.asIdeal.primeCompl
      (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal ⧸
        (Ideal.span {a}).map (algebraMap A (Localization.AtPrime
          (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal))) :=
    hM ▸ inferInstance
  let e := IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)
      (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal ⧸
        (Ideal.span {a}).map (algebraMap A (Localization.AtPrime
          (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal)))
  let f := (IsLocalizedModule.linearEquiv P.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap P.asIdeal.primeCompl (A ⧸ Ideal.span {a}))
      (Algebra.linearMap (A ⧸ Ideal.span {a}) (Localization.AtPrime P.asIdeal))).extendScalarsOfIsLocalization
      P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)
  rw [f.length_eq, length_self_ringEquiv e.toRingEquiv,
    ← Module.length_eq_of_surjective Ideal.Quotient.mk_surjective, ordLoc, Ring.ord,
    Ideal.map_span, Set.image_singleton]

/- English proof (translation)
Unfold `ordMod`. Rewrite using `[ord_ringEquiv (quotQuotComapEquiv a P), quotQuotComapEquiv_mk]`.
-/
theorem ordMod_quot (a b : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b) =
      ordMod (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P) b := by
  unfold ordMod
  rw [ord_ringEquiv (quotQuotComapEquiv a P), quotQuotComapEquiv_mk]

/- English proof (translation)
Establish `hsmul : ∀ (r : A) (n : N), Ideal.Quotient.mk (Ideal.span {a}) r • n = r • n` using `fun r n => by`. Rewrite using `[← Ideal.Quotient.algebraMap_eq, algebraMap_smul (A ⧸ Ideal.span {a})]`. Set `g : Submodule A N → Submodule (A ⧸ Ideal.span {a}) N` to `fun p => { carrier := p add_mem' := p.add_mem zero_mem' := p.zero_mem smul_mem' := fun c n hn => by`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Rewrite using `[hsmul]`.

Conclude with `p.smul_mem r hn }`. Set `iso : Submodule (A ⧸ Ideal.span {a}) N ≃o Submodule A N` to `{ toFun := fun p => p.restrictScalars A invFun := g left_inv := fun p => by ext; rfl right_inv := fun p => by ext; rfl map_rel_iff' := by`. Introduce `p q`. Conclude with `Submodule.restrictScalars_le A }`. Establish `h : Order.krullDim (Submodule (A ⧸ Ideal.span {a}) N) = Order.krullDim (Submodule A N)` using `le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono) (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)`.

Unfold `Module.length`. Use `first`. Consider the case `simp only [h]`. Consider the case `congr 1`.
-/
theorem length_quot_restrict (a : A) (N : Type v) [AddCommGroup N] [Module (A ⧸ Ideal.span {a}) N]
    [Module A N] [IsScalarTower A (A ⧸ Ideal.span {a}) N] :
    length (A ⧸ Ideal.span {a}) N = length A N := by
  have hsmul : ∀ (r : A) (n : N), Ideal.Quotient.mk (Ideal.span {a}) r • n = r • n := fun r n => by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul (A ⧸ Ideal.span {a})]
  let g : Submodule A N → Submodule (A ⧸ Ideal.span {a}) N := fun p =>
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun c n hn => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [hsmul]
        exact p.smul_mem r hn }
  let iso : Submodule (A ⧸ Ideal.span {a}) N ≃o Submodule A N :=
    { toFun := fun p => p.restrictScalars A
      invFun := g
      left_inv := fun p => by ext; rfl
      right_inv := fun p => by ext; rfl
      map_rel_iff' := by
        intro p q
        exact Submodule.restrictScalars_le A }
  have h : Order.krullDim (Submodule (A ⧸ Ideal.span {a}) N) = Order.krullDim (Submodule A N) :=
    le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
      (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
  unfold Module.length
  first
    | simp only [h]
    | congr 1

end ReciprocityTheory.ChartRestriction.G.AI
