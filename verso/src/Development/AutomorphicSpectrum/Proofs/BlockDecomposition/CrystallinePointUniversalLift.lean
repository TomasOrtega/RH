import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueLiftOfNilpotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueHom
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerHom

/- English proof (translation)
Use `choose r hr using h`. Conclude with `⟨fun m => Nat.rec u (fun _ z => r z) m, rfl, fun m => hr _⟩`.
-/
theorem exists_roots {R : Type} [CommRing R] {l : ℕ} (h : ∀ x : R, ∃ y, y ^ l = x) (u : R) :
    ∃ y : ℕ → R, y 0 = u ∧ ∀ m, y (m + 1) ^ l = y m := by
  choose r hr using h
  exact ⟨fun m => Nat.rec u (fun _ z => r z) m, rfl, fun m => hr _⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact h0`. Consider the case `succ m ih => exact h _ _ (by rw [hy, hz, ih])`.
-/
theorem roots_unique {R : Type} [CommRing R] {l : ℕ} (h : ∀ x y : R, x ^ l = y ^ l → x = y) {y z : ℕ → R}
    (h0 : y 0 = z 0) (hy : ∀ m, y (m + 1) ^ l = y m) (hz : ∀ m, z (m + 1) ^ l = z m) (m : ℕ) : y m = z m := by
  induction m with
  | zero => exact h0
  | succ m ih => exact h _ _ (by rw [hy, hz, ih])

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ l m, pow_mul, pow_mul, pow_mul, ← ih, ← hF, ← hF, ← hF, map_sub]`.
-/
theorem pow_sub_pow {R : Type} [CommRing R] {l : ℕ} (F : R →+* R) (hF : ∀ x, F x = x ^ l) (x y : R) (m : ℕ) :
    x ^ l ^ m - y ^ l ^ m = (x - y) ^ l ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ l m, pow_mul, pow_mul, pow_mul, ← ih, ← hF, ← hF, ← hF, map_sub]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ' l m, pow_mul, hx, ih]`.
-/
theorem iter_root {R : Type} [CommRing R] {l : ℕ} {x : ℕ → R} (hx : ∀ m, x (m + 1) ^ l = x m) (m : ℕ) :
    x m ^ l ^ m = x 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ' l m, pow_mul, hx, ih]

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pow_char (A : PAlg l) (x : A.A) : A.frob x = x ^ l := rfl

/- English proof (translation)
The claim follows from `A.frob_bijective.1 h`.
-/
theorem pow_inj (A : PAlg l) (x y : A.A) (h : x ^ l = y ^ l) : x = y := A.frob_bijective.1 h

/- English proof (translation)
The claim follows from `A.frob_bijective.2 x`.
-/
theorem pow_surj (A : PAlg l) (x : A.A) : ∃ y, y ^ l = x := A.frob_bijective.2 x

/- English proof (translation)
Establish `hl : 1 < l` using `(Fact.out : l.Prime).one_lt`. Establish `hH : IsHausdorff (Ideal.span {A.s (pFlat l)}) A.A` using `A.compl.toIsHausdorff`. Use `sub_eq_zero.1 (hH.haus' _ fun n => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.zero, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id, ← iter_root hx n, ← iter_root hy n, pow_sub_pow A.frob (pow_char A)]`. Conclude with `Ideal.pow_le_pow_right (Nat.lt_pow_self hl).le (Ideal.pow_mem_pow (h n) _)`.
-/
theorem eq_of_roots_mod (A : PAlg l) {x y : ℕ → A.A} (hx : ∀ m, x (m + 1) ^ l = x m) (hy : ∀ m, y (m + 1) ^ l = y m)
    (h : ∀ m, x m - y m ∈ Ideal.span {A.pi}) : x 0 = y 0 := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hH : IsHausdorff (Ideal.span {A.s (pFlat l)}) A.A := A.compl.toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun n => ?_)
  rw [SModEq.zero, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id, ← iter_root hx n, ← iter_root hy n,
    pow_sub_pow A.frob (pow_char A)]
  exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl).le (Ideal.pow_mem_pow (h n) _)

/- English proof (translation)
Take `⟨z, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Rewrite using `[map_mul, map_natCast]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem mapU_mem {A A' : PAlg l} (φ : A ⟶ A') {x : A.U} (hx : x ∈ Ideal.span {(l : A.U)}) :
    mapU φ x ∈ Ideal.span {(l : A'.U)} := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Take `⟨a, ha⟩` from `(RL.u_mod A).1 (Ideal.Quotient.mk _ x)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite `ha` using `[A.sharpMap_eq]`. Simplify using `using Ideal.Quotient.eq.1 ha`.
-/
theorem exists_sharp_cong (A : PAlg l) (x : A.U) : ∃ a, A.sharp a - x ∈ Ideal.span {(l : A.U)} := by
  obtain ⟨a, ha⟩ := (RL.u_mod A).1 (Ideal.Quotient.mk _ x)
  refine ⟨a, ?_⟩
  rw [A.sharpMap_eq] at ha
  simpa using Ideal.Quotient.eq.1 ha

def modEquiv (A : PAlg l) : (A.A ⧸ Ideal.span {A.pi}) ≃+* A.Un 1 :=
  (Ideal.quotEquivOfEq (RL.u_mod A).2.symm).trans (RingHom.quotientKerEquivOfSurjective (RL.u_mod A).1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem modEquiv_mk (A : PAlg l) (a : A.A) : modEquiv A (Ideal.Quotient.mk _ a) = A.aToU1 a := rfl

def gBar (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) : R →+* A.A ⧸ Ideal.span {A.pi} :=
  ((modEquiv A).symm : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi}).comp ((Ideal.Quotient.mk _).comp g)

/- English proof (translation)
Establish `e : gBar A g r = (modEquiv A).symm (Ideal.Quotient.mk _ (g r))` using `rfl`. Rewrite using `[e, RingEquiv.symm_apply_eq, modEquiv_mk, A.sharpMap_eq, eq_comm, Ideal.Quotient.eq, pow_one]`.
-/
theorem gBar_iff (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) (r : R) (a : A.A) :
    gBar A g r = Ideal.Quotient.mk _ a ↔ A.sharp a - g r ∈ Ideal.span {(l : A.U)} := by
  have e : gBar A g r = (modEquiv A).symm (Ideal.Quotient.mk _ (g r)) := rfl
  rw [e, RingEquiv.symm_apply_eq, modEquiv_mk, A.sharpMap_eq, eq_comm, Ideal.Quotient.eq, pow_one]

open CrystallineSemistableComparison.PAlg in

/- English proof (translation)
Establish `hy : ∀ k, ∃ y : ℕ → A'.A, y 0 = u k ∧ ∀ m, y (m + 1) ^ l = y m` using `fun k => exists_roots (pow_surj A') (u k)`. Use `choose y hy0 hys using hy`. Establish `hc : ∀ k m, ((𝒯.c k (m + 1)).val) ^ l = (𝒯.c k m).val` using `fun k m => by`. Rewrite using `[← Units.val_pow_eq_pow_val, 𝒯.c_succ]`. Establish `ho : ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (pFlat l) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`.

Establish `h1 : ∀ x w, theta0 l w = κ x → gBar A' g (s.a x) = ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (w.coeff 0)`. Introduce `x w hw`. Establish `hcf : (A'.sW w).coeff 0 = A'.s (w.coeff 0)` using `WittVector.map_coeff _ _ _`. Use `(gBar_iff A' g _ _).2 ?_` and prove the remaining obligations. Establish `e1 : g (s.a x) = A'.th (A'.sW w)`.

Rewrite using `[← A'.oC_theta0, hw]`. Conclude with `RingHom.congr_fun hga x`. Establish `e2` using `A'.sharpMap_coeff (A'.sW w)`. Rewrite `e2` using `[hcf, A'.sharpMap_eq]`. Rewrite using `[e1]`.

Simplify using `using Ideal.Quotient.eq.1 e2`. Establish `h2 : ∀ k, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k 0) = gBar A' g (s.T k)` using `fun k => ((gBar_iff A' g _ _).2 (by rw [hy0, hu, sub_self]; exact Ideal.zero_mem _)).symm`. Establish `h3 : ∀ k m, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k (m + 1)) ^ l = Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k m)` using `fun k m => by rw [← map_pow, hys]`. Take `⟨f, ⟨hfo, hfg, hfc⟩, hfu⟩` from `𝒯.univ (A'.A ⧸ Ideal.span {A'.pi}) ((Ideal.Quotient.mk _).comp A'.s) (gBar A' g) (fun k m => Ideal.Quotient.mk _ (y k m)) ho h1 h2 h3`. Take `⟨φ, hφ, hφu⟩` from `GlobalTheory.CompanionTheory.PerfLift.existsUnique_hom 𝒯.A A' f hfo`.

Establish `hφa : ∀ a, Ideal.Quotient.mk (Ideal.span {A'.pi}) (Hom.f φ a) = f a` using `fun a => RingHom.congr_fun hφ a`. Establish `hck : ∀ k, Hom.f φ (𝒯.c k 0).val = u k`. Introduce `k`. Rewrite using `[← hy0 k]`. Use `eq_of_roots_mod A' (x := fun m => Hom.f φ (𝒯.c k m).val) (fun m => ?_) (hys k) fun m => ?_` and prove the remaining obligations.

Rewrite using `[← map_pow, hc]`. Use `Ideal.Quotient.eq.1 ?_` and prove the remaining obligations. Rewrite using `[hφa, hfc]`. Establish `hgφ : (mapU φ).comp 𝒯.g = g`. Establish `hE` using `GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete (Ideal.span {(l : A'.U)}) A'.completeU (MvPolynomial (Fin d) O) s.R (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R)) s.et (g.comp (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R))) ((Ideal.Quotient.mk _).comp g) r …`.

Use `hE.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩` and prove the remaining obligations. Use `MvPolynomial.ringHom_ext (fun o => ?_) fun k => ?_` and prove the remaining obligations. Establish `e1 : 𝒯.g (s.a o) = 𝒯.A.oC (κ o)` using `RingHom.congr_fun 𝒯.hg o`. Establish `e2 : g (s.a o) = A'.oC (κ o)` using `RingHom.congr_fun hga o`. Simplify using `only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]`.

Rewrite using `[e1, e2, mapU_oC]`. Simplify using `only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]`. Rewrite using `[← 𝒯.c_sharp, mapU_sharp, hck, hu]`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_sharp_cong 𝒯.A (𝒯.g r)`.

Establish `e : gBar A' g r = Ideal.Quotient.mk _ (Hom.f φ a)` using `by rw [hφa]; exact (hfg r a ha).symm`. Establish `e1` using `(gBar_iff A' g r _).1 e`. Establish `e2` using `mapU_mem φ ha`. Rewrite `e2` using `[map_sub, mapU_sharp]`. Use `Ideal.Quotient.eq.2 ?_` and prove the remaining obligations.

Establish `e3 : mapU φ (𝒯.g r) - g r = (A'.sharp (Hom.f φ a) - g r) - (A'.sharp (Hom.f φ a) - mapU φ (𝒯.g r))` using `by ring`. Express the relevant statement in the definitionally equal form `mapU φ (𝒯.g r) - g r ∈ _`. Rewrite using `[e3]`. Conclude with `Ideal.sub_mem _ e1 e2`. Use `⟨φ, ⟨hgφ, hck⟩, fun φ' hg' hk' => hφu φ' (hfu _ ⟨?_, ?_, ?_⟩)⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_assoc, Hom.comm]`. Introduce `r a ha`. Establish `e2` using `mapU_mem φ' ha`. Rewrite `e2` using `[map_sub, mapU_sharp]`. Establish `e3 : mapU φ' (𝒯.g r) = g r` using `RingHom.congr_fun hg' r`.

Rewrite `e2` using `[e3]`. Conclude with `((gBar_iff A' g r _).2 e2).symm`. Introduce `k m`. Use `roots_unique (pow_inj A') (y := fun m => Hom.f φ' (𝒯.c k m).val) (z := y k) ((hk' k).trans (hy0 k).symm) (fun m => by` as an intermediate fact. Rewrite using `[← map_pow, hc]) (hys k) m`.

Conclude with `congrArg (Ideal.Quotient.mk _) this`.
-/
theorem core {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (A' : PAlg l)
    (g : s.R →+* A'.U) (hga : g.comp s.a = A'.oC.comp κ) (u : Fin d → A'.A) (hu : ∀ k, A'.sharp (u k) = g (s.T k)) :
    ∃ φ : 𝒯.A ⟶ A', ((mapU φ).comp 𝒯.g = g ∧ ∀ k, Hom.f φ (𝒯.c k 0).val = u k) ∧
      ∀ φ' : 𝒯.A ⟶ A', (mapU φ').comp 𝒯.g = g → (∀ k, Hom.f φ' (𝒯.c k 0).val = u k) → φ' = φ := by
  have hy : ∀ k, ∃ y : ℕ → A'.A, y 0 = u k ∧ ∀ m, y (m + 1) ^ l = y m := fun k => exists_roots (pow_surj A') (u k)
  choose y hy0 hys using hy
  have hc : ∀ k m, ((𝒯.c k (m + 1)).val) ^ l = (𝒯.c k m).val := fun k m => by
    rw [← Units.val_pow_eq_pow_val, 𝒯.c_succ]
  have ho : ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (pFlat l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have h1 : ∀ x w, theta0 l w = κ x → gBar A' g (s.a x) = ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (w.coeff 0) := by
    intro x w hw
    have hcf : (A'.sW w).coeff 0 = A'.s (w.coeff 0) := WittVector.map_coeff _ _ _
    refine (gBar_iff A' g _ _).2 ?_
    have e1 : g (s.a x) = A'.th (A'.sW w) := by
      rw [← A'.oC_theta0, hw]
      exact RingHom.congr_fun hga x
    have e2 := A'.sharpMap_coeff (A'.sW w)
    rw [hcf, A'.sharpMap_eq] at e2
    rw [e1]
    simpa using Ideal.Quotient.eq.1 e2
  have h2 : ∀ k, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k 0) = gBar A' g (s.T k) := fun k =>
    ((gBar_iff A' g _ _).2 (by rw [hy0, hu, sub_self]; exact Ideal.zero_mem _)).symm
  have h3 : ∀ k m, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k (m + 1)) ^ l = Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k m) :=
    fun k m => by rw [← map_pow, hys]
  obtain ⟨f, ⟨hfo, hfg, hfc⟩, hfu⟩ := 𝒯.univ (A'.A ⧸ Ideal.span {A'.pi}) ((Ideal.Quotient.mk _).comp A'.s) (gBar A' g)
    (fun k m => Ideal.Quotient.mk _ (y k m)) ho h1 h2 h3
  obtain ⟨φ, hφ, hφu⟩ := GlobalTheory.CompanionTheory.PerfLift.existsUnique_hom 𝒯.A A' f hfo
  have hφa : ∀ a, Ideal.Quotient.mk (Ideal.span {A'.pi}) (Hom.f φ a) = f a := fun a => RingHom.congr_fun hφ a
  have hck : ∀ k, Hom.f φ (𝒯.c k 0).val = u k := by
    intro k
    rw [← hy0 k]
    refine eq_of_roots_mod A' (x := fun m => Hom.f φ (𝒯.c k m).val) (fun m => ?_) (hys k) fun m => ?_
    · rw [← map_pow, hc]
    · refine Ideal.Quotient.eq.1 ?_
      rw [hφa, hfc]
  have hgφ : (mapU φ).comp 𝒯.g = g := by
    have hE := GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete (Ideal.span {(l : A'.U)}) A'.completeU
      (MvPolynomial (Fin d) O) s.R (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R)) s.et
      (g.comp (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R))) ((Ideal.Quotient.mk _).comp g) rfl
    refine hE.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun o => ?_) fun k => ?_
      · have e1 : 𝒯.g (s.a o) = 𝒯.A.oC (κ o) := RingHom.congr_fun 𝒯.hg o
        have e2 : g (s.a o) = A'.oC (κ o) := RingHom.congr_fun hga o
        simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        rw [e1, e2, mapU_oC]
      · simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        rw [← 𝒯.c_sharp, mapU_sharp, hck, hu]
    · refine RingHom.ext fun r => ?_
      obtain ⟨a, ha⟩ := exists_sharp_cong 𝒯.A (𝒯.g r)
      have e : gBar A' g r = Ideal.Quotient.mk _ (Hom.f φ a) := by rw [hφa]; exact (hfg r a ha).symm
      have e1 := (gBar_iff A' g r _).1 e
      have e2 := mapU_mem φ ha
      rw [map_sub, mapU_sharp] at e2
      refine Ideal.Quotient.eq.2 ?_
      have e3 : mapU φ (𝒯.g r) - g r = (A'.sharp (Hom.f φ a) - g r) - (A'.sharp (Hom.f φ a) - mapU φ (𝒯.g r)) := by ring
      change mapU φ (𝒯.g r) - g r ∈ _
      rw [e3]
      exact Ideal.sub_mem _ e1 e2
  refine ⟨φ, ⟨hgφ, hck⟩, fun φ' hg' hk' => hφu φ' (hfu _ ⟨?_, ?_, ?_⟩)⟩
  · rw [RingHom.comp_assoc, Hom.comm]
  · intro r a ha
    have e2 := mapU_mem φ' ha
    rw [map_sub, mapU_sharp] at e2
    have e3 : mapU φ' (𝒯.g r) = g r := RingHom.congr_fun hg' r
    rw [e3] at e2
    exact ((gBar_iff A' g r _).2 e2).symm
  · intro k m
    have := roots_unique (pow_inj A') (y := fun m => Hom.f φ' (𝒯.c k m).val) (z := y k)
      ((hk' k).trans (hy0 k).symm) (fun m => by
        rw [← map_pow, hc]) (hys k) m
    exact congrArg (Ideal.Quotient.mk _) this

/- English proof (translation)
Introduce `l _ O _ F κ d s 𝒯 T`. Take `⟨g, hg, hgu⟩` from `s.univ (CommRingCat.of T.1.U) T.2.1 (T.1.oC.comp κ) T.2.2`. Establish `hga : g.comp s.a = T.1.oC.comp κ` using `F.ov_uniq (hg ▸ F.ov_map (CommRingCat.ofHom g) s.ov) T.2.2`. Establish `hall : ∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g`. Introduce `φ`.

Use `hgu _ ?_` and prove the remaining obligations. Establish `h1 : F.Pt.map (CommRingCat.ofHom (mapU φ.1)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1` using `congrArg Subtype.val φ.2`. Establish `h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ.1).comp 𝒯.g)) s.y₀ = T.2.1`. Rewrite using `[CommRingCat.ofHom_comp, F.Pt.map_comp]`. Conclude with `h1`.

Conclude with `h2`. Use `⟨g, hg, hall, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨φ, ⟨hφg, hφk⟩, hφu⟩` from `core 𝒯 T.1 g hga u hu`. Establish `hpt : (F.pt κ).map φ 𝒯.obj.2 = T.2`. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `F.Pt.map (CommRingCat.ofHom (mapU φ)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1`. Establish `h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ).comp 𝒯.g)) s.y₀ = T.2.1`. Rewrite using `[hφg]`. Conclude with `hg`. Rewrite `h2` using `[CommRingCat.ofHom_comp, F.Pt.map_comp]`.

Conclude with `h2`. Use `⟨⟨φ, hpt⟩, hφk, fun φ' hk => Subtype.ext (hφu φ'.1 (hall φ') hk)⟩` and prove the remaining obligations.
-/
theorem tower_hom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  intro l _ O _ F κ d s 𝒯 T
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of T.1.U) T.2.1 (T.1.oC.comp κ) T.2.2
  have hga : g.comp s.a = T.1.oC.comp κ :=
    F.ov_uniq (hg ▸ F.ov_map (CommRingCat.ofHom g) s.ov) T.2.2
  have hall : ∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g := by
    intro φ
    refine hgu _ ?_
    have h1 : F.Pt.map (CommRingCat.ofHom (mapU φ.1)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1 :=
      congrArg Subtype.val φ.2
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ.1).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
      exact h1
    exact h2
  refine ⟨g, hg, hall, fun u hu => ?_⟩
  obtain ⟨φ, ⟨hφg, hφk⟩, hφu⟩ := core 𝒯 T.1 g hga u hu
  have hpt : (F.pt κ).map φ 𝒯.obj.2 = T.2 := by
    refine Subtype.ext ?_
    change F.Pt.map (CommRingCat.ofHom (mapU φ)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [hφg]
      exact hg
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp] at h2
    exact h2
  refine ⟨⟨φ, hpt⟩, hφk, fun φ' hk => Subtype.ext (hφu φ'.1 (hall φ') hk)⟩

end GlobalTheory.CompanionTheory.TowerHom
