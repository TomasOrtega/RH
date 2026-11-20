import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentialsStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) : Submodule (WittVector p k) N where
  carrier := {m | ∃ n ∈ X, F n = m}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, X.add_mem ha hb, map_add F a b⟩
  zero_mem' := ⟨0, X.zero_mem, map_zero F⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
    refine ⟨d • a, X.smul_mem d ha, ?_⟩
    rw [map_smulₛₗ, WittVector.frobeniusEquiv_apply]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) (m : N) : m ∈ frobImage F X ↔ ∃ n ∈ X, F n = m := Iff.rfl

/- English proof (translation)
Use `haveI : RingHomSurjective (WittVector.frobenius : WittVector p k →+* WittVector p k) := ⟨fun c => by`. Take `⟨d, rfl⟩` from `(WittVector.frobeniusEquiv p k).surjective c`. Conclude with `⟨d, by rw [WittVector.frobeniusEquiv_apply]⟩⟩`. Set `f : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] frobImage F ⊤` to `LinearMap.codRestrict (frobImage F ⊤) F (fun c => ⟨c, Submodule.mem_top, rfl⟩)`. Establish `hf : Function.Bijective f`.

Use `⟨fun a b h => hF (congrArg Subtype.val h), ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨m, n, -, rfl⟩`. Conclude with `⟨n, rfl⟩`. Establish `hX : Submodule.orderIsoMapComapOfBijective f hf X = Submodule.comap (frobImage F ⊤).subtype (frobImage F X)`. Use extensionality with `⟨m, hm⟩`.

Express the relevant statement in the definitionally equal form `(⟨m, hm⟩ : frobImage F ⊤) ∈ Submodule.map f X ↔ _`. Rewrite using `[Submodule.mem_map, Submodule.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, h⟩`. Conclude with `⟨n, hn, congrArg Subtype.val h⟩`.

Introduce and unpack `⟨n, hn, h⟩`. Conclude with `⟨n, hn, Subtype.ext h⟩`. Rewrite using `[Module.length_quotient, Module.length_quotient, ← hX, Order.coheight_orderIso]`.
-/
theorem length_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (hF : Function.Injective F)
    (X : Submodule (WittVector p k) N) :
    Module.length (WittVector p k)
        (frobImage F ⊤ ⧸ Submodule.comap (frobImage F ⊤).subtype (frobImage F X)) =
      Module.length (WittVector p k) (N ⧸ X) := by
  haveI : RingHomSurjective (WittVector.frobenius : WittVector p k →+* WittVector p k) :=
    ⟨fun c => by
      obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
      exact ⟨d, by rw [WittVector.frobeniusEquiv_apply]⟩⟩
  let f : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] frobImage F ⊤ :=
    LinearMap.codRestrict (frobImage F ⊤) F (fun c => ⟨c, Submodule.mem_top, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => hF (congrArg Subtype.val h), ?_⟩
    rintro ⟨m, n, -, rfl⟩
    exact ⟨n, rfl⟩
  have hX : Submodule.orderIsoMapComapOfBijective f hf X =
      Submodule.comap (frobImage F ⊤).subtype (frobImage F X) := by
    ext ⟨m, hm⟩
    change (⟨m, hm⟩ : frobImage F ⊤) ∈ Submodule.map f X ↔ _
    rw [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, congrArg Subtype.val h⟩
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, Subtype.ext h⟩
  rw [Module.length_quotient, Module.length_quotient, ← hX, Order.coheight_orderIso]

/- English proof (translation)
Take `⟨s, hs'⟩` from `(Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) N).FG)`. Use `⟨⟨s.image θ, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, eq_top_iff]`. Introduce and unpack `u -`. Take `⟨n, rfl⟩` from `hθ u`.

Establish `hn : n ∈ Submodule.span (WittVector p k) (s : Set N)` using `hs' ▸ Submodule.mem_top`. Proceed by induction on `hn using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Take `⟨b, rfl⟩` from `(WittVector.frobeniusEquiv p k).surjective a`. Rewrite using `[WittVector.frobeniusEquiv_apply, hs]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem finite_of_frob_surj {N U : Type} [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Finite (WittVector p k) N] [AddCommGroup U] [Module k U] (θ : N →+ U)
    (hθ : Function.Surjective θ)
    (hs : ∀ (a : WittVector p k) n, θ (WittVector.frobenius a • n) = WittVector.constantCoeff a • θ n) :
    Module.Finite k U := by
  classical
  obtain ⟨s, hs'⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) N).FG)
  refine ⟨⟨s.image θ, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro u -
  obtain ⟨n, rfl⟩ := hθ u
  have hn : n ∈ Submodule.span (WittVector p k) (s : Set N) := hs' ▸ Submodule.mem_top
  induction hn using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective a
    rw [WittVector.frobeniusEquiv_apply, hs]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

/- English proof (translation)
Take `⟨n, q', h1, h2⟩` from `hq`. Establish `huv : ∀ m : T.M G, T.map q (T.map q' m) = p ^ n • m`. Introduce `m`. Rewrite using `[← LinearMap.comp_apply, ← (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H G trivial trivial trivial).2.1 q q', h1, (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).2.2.2.2.1 n (𝟙 G) m, (GlobalTheory.T.di …`. Establish `hvu : ∀ m : T.M H, T.map q' (T.map q m) = p ^ n • m`.

Introduce `m`. Rewrite using `[← LinearMap.comp_apply, ← (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k H G H trivial trivial trivial).2.1 q' q, h2, (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k H H H trivial trivial trivial).2.2.2.2.1 n (𝟙 H) m, (GlobalTheory.T.di …`. Establish `hinj : Function.Injective (T.map q)`. Introduce `a b hab`. Establish `h` using `congrArg (T.map q') hab`.

Rewrite `h` using `[hvu a, hvu b]`. Establish `h0 : p ^ n • (a - b) = 0` using `by rw [smul_sub, h, sub_self]`. Conclude with `sub_eq_zero.1 ((GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k H H H trivial trivial trivial).2.2.2.2.2.2.2.2 n _ h0)`. Establish `LA` using `(GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)).1 (T.map q) (T.map q') hinj`. Establish `LB` using `(GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M G) (T.M G)).2.1 (T.base.free G trivial) (T.base.finite G trivial) n (T.map q ∘ₗ T.map q') (fun a => huv a)`.

Rewrite `LA` using `[LB]`. Establish `hfin : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤`. Introduce `h`. Rewrite `LA` using `[h, top_add]`. Conclude with `ENat.coe_ne_top _ LA`.

Use `⟨hinj, hfin, ?_⟩` and prove the remaining obligations. Take `⟨θ, hθ⟩` from `GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k`. Establish `dimω : ∀ K : PDivGroup p k, Module.length (WittVector p k) (T.M K ⧸ frobImage (T.F K) ⊤) = Module.finrank k K.omega`. Introduce `K`. Take `⟨-, hs, hk, hl, -⟩` from `hθ K`.

Use `haveI : Module.Finite (WittVector p k) (T.M K) := T.base.finite K trivial`. Use `haveI := finite_of_frob_surj (θ K) hs hl`. Use `(GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M K) K.omega (WittVector.frobeniusEquiv p k) (θ K) hs ?_ (frobImage (T.F K) ⊤)).2 ?_` and prove the remaining obligations. Introduce `a m`. Rewrite using `[WittVector.frobeniusEquiv_apply]`.

Conclude with `hl a m`. Introduce `m`. Rewrite using `[hk, mem_frobImage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, -, h⟩`.

Conclude with `⟨c, h.symm⟩`. Introduce and unpack `⟨c, h⟩`. Conclude with `⟨c, Submodule.mem_top, h.symm⟩`. Establish `hF : ∀ y : T.M H, T.map q (T.F H y) = T.F G (T.map q y)` using `fun y => (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H G trivial trivial trivial).2.2.2.2.2.2.1 q y`. Use `set X := LinearMap.range (T.map q) with hXdef`.

Use `set L3 := frobImage (T.F G) X with hL3`. Use `set FG := frobImage (T.F G) ⊤ with hFG`. Use `set FH := frobImage (T.F H) ⊤ with hFH`. Establish `hle : L3 ≤ FG`. Introduce and unpack `m ⟨c, -, rfl⟩`.

Conclude with `⟨c, Submodule.mem_top, rfl⟩`. Establish `hr1 : LinearMap.range (FG.subtype ∘ₗ (Submodule.comap FG.subtype L3).subtype) = L3`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hle]`. Establish `hr2 : LinearMap.range (T.map q ∘ₗ FH.subtype) = L3`. Use extensionality with `m`.

Rewrite using `[LinearMap.mem_range, hL3, mem_frobImage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, y, -, rfl⟩, rfl⟩`. Conclude with `⟨T.map q y, LinearMap.mem_range.2 ⟨y, rfl⟩, (hF y).symm⟩`. Introduce and unpack `⟨z, hz, rfl⟩`.

Take `⟨y, rfl⟩` from `LinearMap.mem_range.1 hz`. Conclude with `⟨⟨T.F H y, y, Submodule.mem_top, rfl⟩, hF y⟩`. Establish `eA` using `(GlobalTheory.T.witt_module_length_composition p k (T.M G) FG (Submodule.comap FG.subtype L3)).1 FG.subtype (Submodule.comap FG.subtype L3).subtype (Submodule.injective_subtype _)`. Rewrite `eA` using `[hr1, Submodule.range_subtype, Submodule.range_subtype]`. Establish `eB` using `(GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) FH).1 (T.map q) FH.subtype hinj`.

Rewrite `eB` using `[hr2, Submodule.range_subtype]`. Establish `hC : Module.length (WittVector p k) (FG ⧸ Submodule.comap FG.subtype L3) = Module.length (WittVector p k) (T.M G ⧸ X)` using `length_frobImage (T.F G) (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1 X`. Rewrite `eA` using `[hC, hFG, dimω G]`. Rewrite `eB` using `[hFH, dimω H]`. Take `⟨d, hd⟩` from `ENat.ne_top_iff_exists.1 hfin`.

Rewrite `eA`, `eB` using `[← hd]`. Establish `h' : ((Module.finrank k G.omega + d : ℕ) : ℕ∞) = ((d + Module.finrank k H.omega : ℕ) : ℕ∞)`. Use `push_cast`. Conclude with `eA.symm.trans eB`. Establish `h''` using `Nat.cast_injective h'`.

Use linear arithmetic over natural numbers and integers.
-/
theorem isog_core (T : Theory p) {G H : PDivGroup p k} (q : G ⟶ H) (hq : IsIsog q) :
    Function.Injective (T.map q) ∧
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
    Module.finrank k G.omega = Module.finrank k H.omega := by
  obtain ⟨n, q', h1, h2⟩ := hq
  have huv : ∀ m : T.M G, T.map q (T.map q' m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H G trivial trivial trivial).2.1 q q', h1,
      (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).2.2.2.2.1 n (𝟙 G) m,
      (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).1, LinearMap.id_apply]
  have hvu : ∀ m : T.M H, T.map q' (T.map q m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k H G H trivial trivial trivial).2.1 q' q, h2,
      (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k H H H trivial trivial trivial).2.2.2.2.1 n (𝟙 H) m,
      (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k H H H trivial trivial trivial).1, LinearMap.id_apply]
  have hinj : Function.Injective (T.map q) := by
    intro a b hab
    have h := congrArg (T.map q') hab
    rw [hvu a, hvu b] at h
    have h0 : p ^ n • (a - b) = 0 := by rw [smul_sub, h, sub_self]
    exact sub_eq_zero.1 ((GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k H H H trivial trivial trivial).2.2.2.2.2.2.2.2 n _ h0)
  have LA := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)).1 (T.map q) (T.map q') hinj
  have LB := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M G) (T.M G)).2.1 (T.base.free G trivial)
    (T.base.finite G trivial) n (T.map q ∘ₗ T.map q') (fun a => huv a)
  rw [LB] at LA
  have hfin : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ := by
    intro h
    rw [h, top_add] at LA
    exact ENat.coe_ne_top _ LA
  refine ⟨hinj, hfin, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  have dimω : ∀ K : PDivGroup p k,
      Module.length (WittVector p k) (T.M K ⧸ frobImage (T.F K) ⊤) = Module.finrank k K.omega := by
    intro K
    obtain ⟨-, hs, hk, hl, -⟩ := hθ K
    haveI : Module.Finite (WittVector p k) (T.M K) := T.base.finite K trivial
    haveI := finite_of_frob_surj (θ K) hs hl
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M K) K.omega (WittVector.frobeniusEquiv p k) (θ K) hs ?_
      (frobImage (T.F K) ⊤)).2 ?_
    · intro a m
      rw [WittVector.frobeniusEquiv_apply]
      exact hl a m
    · intro m
      rw [hk, mem_frobImage]
      constructor
      · rintro ⟨c, -, h⟩
        exact ⟨c, h.symm⟩
      · rintro ⟨c, h⟩
        exact ⟨c, Submodule.mem_top, h.symm⟩
  have hF : ∀ y : T.M H, T.map q (T.F H y) = T.F G (T.map q y) :=
    fun y => (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H G trivial trivial trivial).2.2.2.2.2.2.1 q y
  set X := LinearMap.range (T.map q) with hXdef
  set L3 := frobImage (T.F G) X with hL3
  set FG := frobImage (T.F G) ⊤ with hFG
  set FH := frobImage (T.F H) ⊤ with hFH
  have hle : L3 ≤ FG := by
    rintro m ⟨c, -, rfl⟩
    exact ⟨c, Submodule.mem_top, rfl⟩
  have hr1 : LinearMap.range (FG.subtype ∘ₗ (Submodule.comap FG.subtype L3).subtype) = L3 := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  have hr2 : LinearMap.range (T.map q ∘ₗ FH.subtype) = L3 := by
    ext m
    rw [LinearMap.mem_range, hL3, mem_frobImage]
    constructor
    · rintro ⟨⟨x, y, -, rfl⟩, rfl⟩
      exact ⟨T.map q y, LinearMap.mem_range.2 ⟨y, rfl⟩, (hF y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hz
      exact ⟨⟨T.F H y, y, Submodule.mem_top, rfl⟩, hF y⟩
  have eA := (GlobalTheory.T.witt_module_length_composition p k (T.M G) FG (Submodule.comap FG.subtype L3)).1
    FG.subtype (Submodule.comap FG.subtype L3).subtype (Submodule.injective_subtype _)
  rw [hr1, Submodule.range_subtype, Submodule.range_subtype] at eA
  have eB := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) FH).1 (T.map q) FH.subtype hinj
  rw [hr2, Submodule.range_subtype] at eB
  have hC : Module.length (WittVector p k) (FG ⧸ Submodule.comap FG.subtype L3) =
      Module.length (WittVector p k) (T.M G ⧸ X) :=
    length_frobImage (T.F G) (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1 X
  rw [hC, hFG, dimω G] at eA
  rw [hFH, dimω H] at eB
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hd] at eA eB
  have h' : ((Module.finrank k G.omega + d : ℕ) : ℕ∞) = ((d + Module.finrank k H.omega : ℕ) : ℕ∞) := by
    push_cast
    exact eA.symm.trans eB
  have h'' := Nat.cast_injective h'
  omega

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu

/- English proof (translation)
Introduce `p _ T k _ _ _ G H q hq`. Take `⟨h1, h2, h3⟩` from `IsogDim.isog_core T q hq`. Take `⟨-, hd, -⟩` from `GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq`. Conclude with `⟨h1, h2, h3, (IsogDim.isog_core T (dualHom G H q) hd).2.2.symm⟩`.
-/
theorem isog_finrank_omega : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Injective (T.map q) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧ Module.finrank k G.omega = Module.finrank k H.omega ∧ Module.finrank k G.dual.omega = Module.finrank k H.dual.omega := by
  intro p _ T k _ _ _ G H q hq
  obtain ⟨h1, h2, h3⟩ := IsogDim.isog_core T q hq
  obtain ⟨-, hd, -⟩ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
  exact ⟨h1, h2, h3, (IsogDim.isog_core T (dualHom G H q) hd).2.2.symm⟩

end GlobalTheory.Dieu
