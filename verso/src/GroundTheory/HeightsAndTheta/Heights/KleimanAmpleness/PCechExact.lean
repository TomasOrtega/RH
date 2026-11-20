import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCechDSq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegLocExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

namespace Cech

section HdegMk

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {deg : ∀ I, Submodule R (G I)}
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {i : ℕ}

def Hdeg.mk (z : cocyDeg G deg ρ i) : Hdeg G deg ρ i := Submodule.Quotient.mk z

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_eq_zero _`.
-/
theorem Hdeg_mk_eq_zero (z : cocyDeg G deg ρ i) : Hdeg.mk z = 0 ↔ z.1 ∈ bdryDeg G deg ρ i :=
  Submodule.Quotient.mk_eq_zero _

/- English proof (translation)
The claim follows from `Submodule.Quotient.eq _`.
-/
theorem Hdeg_mk_eq_mk (z z' : cocyDeg G deg ρ i) :
    Hdeg.mk z = Hdeg.mk z' ↔ z.1 - z'.1 ∈ bdryDeg G deg ρ i :=
  Submodule.Quotient.eq _

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_surjective _ y`.
-/
theorem Hdeg_mk_surjective (y : Hdeg G deg ρ i) : ∃ z : cocyDeg G deg ρ i, Hdeg.mk z = y :=
  Submodule.Quotient.mk_surjective _ y

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_zero _`.
-/
theorem Hdeg_mk_zero : Hdeg.mk (0 : cocyDeg G deg ρ i) = 0 :=
  Submodule.Quotient.mk_zero _

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_add _`.
-/
theorem Hdeg_mk_add (a b : cocyDeg G deg ρ i) : Hdeg.mk (a + b) = Hdeg.mk a + Hdeg.mk b :=
  Submodule.Quotient.mk_add _

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_smul _ _ _`.
-/
theorem Hdeg_mk_smul (r : R) (a : cocyDeg G deg ρ i) : Hdeg.mk (r • a) = r • Hdeg.mk a :=
  Submodule.Quotient.mk_smul _ _ _

end HdegMk

section LongExact

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A B C : Cell U → Type v}
  [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
  {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J}
  {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
  {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
  {dA : ∀ I, Submodule R (A I)} {dB : ∀ I, Submodule R (B I)} {dC : ∀ I, Submodule R (C I)}
  {φ : ∀ I, A I →ₗ[R] B I} {ψ : ∀ I, B I →ₗ[R] C I}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h I => h I (Set.mem_univ _), fun h I _ => h I⟩`.
-/
theorem mem_Cdeg_iff {i : ℕ} {s : Cochain A i} : s ∈ Cdeg A dA i ↔ ∀ I, s I ∈ dA I.1 :=
  ⟨fun h I => h I (Set.mem_univ _), fun h I _ => h I⟩

/- English proof (translation)
The claim follows from `mem_Cdeg_iff.2 fun I => hφd I.1 _ (mem_Cdeg_iff.1 hs I)`.
-/
theorem mapC_mem_Cdeg (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) {i : ℕ} {s : Cochain A i}
    (hs : s ∈ Cdeg A dA i) : mapC φ i s ∈ Cdeg B dB i :=
  mem_Cdeg_iff.2 fun I => hφd I.1 _ (mem_Cdeg_iff.1 hs I)

/- English proof (translation)
Introduce `_ _ h` and use `funext fun I => hinj I.1 (congrFun h I)`.
-/
theorem mapC_injective (hinj : ∀ I, Function.Injective (φ I)) (i : ℕ) :
    Function.Injective (mapC φ i) :=
  fun _ _ h => funext fun I => hinj I.1 (congrFun h I)

/- English proof (translation)
The claim follows from `funext fun I => hcomp I.1 (s I)`.
-/
theorem mapC_mapC_eq_zero (hcomp : ∀ I x, ψ I (φ I x) = 0) (i : ℕ) (s : Cochain A i) :
    mapC ψ i (mapC φ i s) = 0 :=
  funext fun I => hcomp I.1 (s I)

/- English proof (translation)
Use `choose t ht hts using fun I : Idx U i => hmid I.1 (s I) (mem_Cdeg_iff.1 hs I) (congrFun h0 I)`. Conclude with `⟨t, mem_Cdeg_iff.2 ht, funext hts⟩`.
-/
theorem exists_mapC_eq (hmid : ∀ I, ∀ x ∈ dB I, ψ I x = 0 → ∃ y ∈ dA I, φ I y = x) {i : ℕ}
    {s : Cochain B i} (hs : s ∈ Cdeg B dB i) (h0 : mapC ψ i s = 0) :
    ∃ t ∈ Cdeg A dA i, mapC φ i t = s := by
  choose t ht hts using fun I : Idx U i => hmid I.1 (s I) (mem_Cdeg_iff.1 hs I) (congrFun h0 I)
  exact ⟨t, mem_Cdeg_iff.2 ht, funext hts⟩

/- English proof (translation)
Use `choose t ht hts using fun I : Idx U i => hsurj I.1 (s I) (mem_Cdeg_iff.1 hs I)`. Conclude with `⟨t, mem_Cdeg_iff.2 ht, funext hts⟩`.
-/
theorem exists_mapC_eq_of_mem (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z) {i : ℕ}
    {s : Cochain C i} (hs : s ∈ Cdeg C dC i) : ∃ t ∈ Cdeg B dB i, mapC ψ i t = s := by
  choose t ht hts using fun I : Idx U i => hsurj I.1 (s I) (mem_Cdeg_iff.1 hs I)
  exact ⟨t, mem_Cdeg_iff.2 ht, funext hts⟩

/- English proof (translation)
Use `mem_Cdeg_iff.2 fun J => ?_` and prove the remaining obligations. Rewrite using `[d_apply]`. Conclude with `Submodule.sum_mem _ fun j _ => zsmul_mem (hρB _ _ _ _ (mem_Cdeg_iff.1 hs _)) _`.
-/
theorem d_mem_Cdeg (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J) {i : ℕ} {s : Cochain B i}
    (hs : s ∈ Cdeg B dB i) : d B ρB i s ∈ Cdeg B dB (i + 1) := by
  refine mem_Cdeg_iff.2 fun J => ?_
  rw [d_apply]
  exact Submodule.sum_mem _ fun j _ => zsmul_mem (hρB _ _ _ _ (mem_Cdeg_iff.1 hs _)) _

/- English proof (translation)
Consider the cases of `i with`. Consider the case `zero`. Establish `h0 : s ∈ (⊥ : Submodule R (Cochain C 0))` using `hs`. Rewrite `h0` using `[Submodule.mem_bot]`. Conclude with `⟨0, Submodule.zero_mem _, Submodule.zero_mem _, by rw [map_zero, h0], map_zero _⟩`.

Consider the case `succ k`. Take `⟨y'', hy'', rfl⟩` from `hs`. Take `⟨y, hy, rfl⟩` from `exists_mapC_eq_of_mem hsurj hy''`. Conclude with `⟨d B ρB k y, ⟨y, hy, rfl⟩, d_mem_Cdeg hρB hy, mapC_d ψ hψ k y, hddB k y⟩`.
-/
theorem exists_bdryDeg_of_mem_bdryDeg (hψ : ∀ I J h m, ψ J (ρB I J h m) = ρC I J h (ψ I m))
    (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z)
    (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J)
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) {i : ℕ}
    {s : Cochain C i} (hs : s ∈ bdryDeg C dC ρC i) :
    ∃ x, x ∈ bdryDeg B dB ρB i ∧ x ∈ Cdeg B dB i ∧ mapC ψ i x = s ∧ d B ρB i x = 0 := by
  cases i with
  | zero =>
    have h0 : s ∈ (⊥ : Submodule R (Cochain C 0)) := hs
    rw [Submodule.mem_bot] at h0
    exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, by rw [map_zero, h0], map_zero _⟩
  | succ k =>
    obtain ⟨y'', hy'', rfl⟩ := hs
    obtain ⟨y, hy, rfl⟩ := exists_mapC_eq_of_mem hsurj hy''
    exact ⟨d B ρB k y, ⟨y, hy, rfl⟩, d_mem_Cdeg hρB hy, mapC_d ψ hψ k y, hddB k y⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `w`. Express the relevant statement in the definitionally equal form `mapC φ i z.1 = w at h`. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem mapHdeg_mk (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) {i : ℕ} (z : cocyDeg A dA ρA i)
    (w : cocyDeg B dB ρB i) (h : mapC φ i z.1 = w.1) :
    mapHdeg dA dB φ hφ hφd i (Hdeg.mk z) = Hdeg.mk w := by
  obtain ⟨w, hw⟩ := w
  change mapC φ i z.1 = w at h
  subst h
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨LinearMap.mem_ker.2 (by rw [← mapC_d φ hφ, LinearMap.mem_ker.1 hs.1, map_zero]), mapC_mem_Cdeg hφd hs.2⟩`.
-/
theorem mapC_mem_cocyDeg (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) {i : ℕ} {s : Cochain A i}
    (hs : s ∈ cocyDeg A dA ρA i) : mapC φ i s ∈ cocyDeg B dB ρB i :=
  ⟨LinearMap.mem_ker.2 (by rw [← mapC_d φ hφ, LinearMap.mem_ker.1 hs.1, map_zero]),
    mapC_mem_Cdeg hφd hs.2⟩

/- English proof (translation)
Introduce `y`. Take `⟨z, rfl⟩` from `Hdeg_mk_surjective y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[mapHdeg_mk hψ hψd z ⟨_, mapC_mem_cocyDeg hψ hψd z.2⟩ rfl, Hdeg_mk_eq_zero]`.

Express the relevant statement in the definitionally equal form `mapC ψ i z.1 ∈ bdryDeg C dC ρC i at h`. Take `⟨x, hxb, hx, hψx, hdx⟩` from `exists_bdryDeg_of_mem_bdryDeg hψ hsurj hρB hddB h`. Take `⟨t, ht, htz⟩` from `exists_mapC_eq hmid (sub_mem z.2.2 hx) (by rw [map_sub, hψx]; exact sub_self _)`. Establish `htc : t ∈ cocyDeg A dA ρA i`. Use `⟨LinearMap.mem_ker.2 (mapC_injective hinj (i + 1) ?_), ht⟩` and prove the remaining obligations.

Rewrite using `[mapC_d φ hφ, htz, map_sub, LinearMap.mem_ker.1 z.2.1, hdx, sub_zero, map_zero]`. Use `⟨Hdeg.mk ⟨t, htc⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mapHdeg_mk hφ hφd ⟨t, htc⟩ ⟨_, mapC_mem_cocyDeg hφ hφd htc⟩ rfl, Hdeg_mk_eq_mk]`. Express the relevant statement in the definitionally equal form `mapC φ i t - z.1 ∈ _`. Rewrite using `[htz, sub_sub_cancel_left]`.

Conclude with `Submodule.neg_mem _ hxb`. Introduce and unpack `⟨y, hy⟩`. Take `⟨t, rfl⟩` from `Hdeg_mk_surjective y`. Rewrite using `[← hy, mapHdeg_mk hφ hφd t ⟨_, mapC_mem_cocyDeg hφ hφd t.2⟩ rfl, mapHdeg_mk hψ hψd _ ⟨_, mapC_mem_cocyDeg hψ hψd (mapC_mem_cocyDeg hφ hφd t.2)⟩ rfl, Hdeg_mk_eq_zero]`. Express the relevant statement in the definitionally equal form `mapC ψ i (mapC φ i t.1) ∈ _`.

Rewrite using `[mapC_mapC_eq_zero hcomp]`. Conclude with `Submodule.zero_mem _`.
-/
theorem exact_mapHdeg (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hψ : ∀ I J h m, ψ J (ρB I J h m) = ρC I J h (ψ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) (hψd : ∀ I m, m ∈ dB I → ψ I m ∈ dC I)
    (hinj : ∀ I, Function.Injective (φ I)) (hcomp : ∀ I x, ψ I (φ I x) = 0)
    (hmid : ∀ I, ∀ x ∈ dB I, ψ I x = 0 → ∃ y ∈ dA I, φ I y = x)
    (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z)
    (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J)
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) (i : ℕ) :
    Function.Exact (mapHdeg dA dB φ hφ hφd i) (mapHdeg dB dC ψ hψ hψd i) := by
  intro y
  obtain ⟨z, rfl⟩ := Hdeg_mk_surjective y
  constructor
  · intro h
    rw [mapHdeg_mk hψ hψd z ⟨_, mapC_mem_cocyDeg hψ hψd z.2⟩ rfl, Hdeg_mk_eq_zero] at h
    change mapC ψ i z.1 ∈ bdryDeg C dC ρC i at h
    obtain ⟨x, hxb, hx, hψx, hdx⟩ := exists_bdryDeg_of_mem_bdryDeg hψ hsurj hρB hddB h
    obtain ⟨t, ht, htz⟩ := exists_mapC_eq hmid (sub_mem z.2.2 hx)
      (by rw [map_sub, hψx]; exact sub_self _)
    have htc : t ∈ cocyDeg A dA ρA i := by
      refine ⟨LinearMap.mem_ker.2 (mapC_injective hinj (i + 1) ?_), ht⟩
      rw [mapC_d φ hφ, htz, map_sub, LinearMap.mem_ker.1 z.2.1, hdx, sub_zero, map_zero]
    refine ⟨Hdeg.mk ⟨t, htc⟩, ?_⟩
    rw [mapHdeg_mk hφ hφd ⟨t, htc⟩ ⟨_, mapC_mem_cocyDeg hφ hφd htc⟩ rfl, Hdeg_mk_eq_mk]
    change mapC φ i t - z.1 ∈ _
    rw [htz, sub_sub_cancel_left]
    exact Submodule.neg_mem _ hxb
  · rintro ⟨y, hy⟩
    obtain ⟨t, rfl⟩ := Hdeg_mk_surjective y
    rw [← hy, mapHdeg_mk hφ hφd t ⟨_, mapC_mem_cocyDeg hφ hφd t.2⟩ rfl,
      mapHdeg_mk hψ hψd _ ⟨_, mapC_mem_cocyDeg hψ hψd (mapC_mem_cocyDeg hφ hφd t.2)⟩ rfl,
      Hdeg_mk_eq_zero]
    change mapC ψ i (mapC φ i t.1) ∈ _
    rw [mapC_mapC_eq_zero hcomp]
    exact Submodule.zero_mem _

/- English proof (translation)
Use `⟨?_, fun i => ⟨exact_mapHdeg hφ hψ hφd hψd hinj hcomp hmid hsurj hρB hddB i, ?_⟩⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero _).2 fun y hy => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `Hdeg_mk_surjective y`. Rewrite `hy` using `[mapHdeg_mk hφ hφd z ⟨_, mapC_mem_cocyDeg hφ hφd z.2⟩ rfl, Hdeg_mk_eq_zero]`. Establish `h0 : mapC φ 0 z.1 ∈ (⊥ : Submodule R (Cochain B 0))` using `hy`.

Rewrite `h0` using `[Submodule.mem_bot, ← map_zero (mapC φ 0)]`. Establish `hz : z = 0` using `Subtype.ext (mapC_injective hinj 0 h0)`. Rewrite using `[hz, Hdeg_mk_zero]`. Use `choose lift hlift_mem hlift using fun z : cocyDeg C dC ρC i => exists_mapC_eq_of_mem hsurj z.2.2`. Use `choose w hw_mem hw using fun z : cocyDeg C dC ρC i => exists_mapC_eq hmid (d_mem_Cdeg hρB (hlift_mem z)) (by rw [mapC_d ψ hψ, hlift]; exact LinearMap.mem_ker.1 z.2.1)`.

Establish `hw_cocy : ∀ z, w z ∈ cocyDeg A dA ρA (i + 1)` using `fun z => ⟨LinearMap.mem_ker.2 (mapC_injective hinj (i + 1 + 1) (by`. Rewrite using `[mapC_d φ hφ, hw, hddB, map_zero])), hw_mem z⟩`. Establish `key : ∀ (z : cocyDeg C dC ρC i) (x : Cochain B i), x ∈ Cdeg B dB i → mapC ψ i x = z.1 → ∀ y : cocyDeg A dA ρA (i + 1), mapC φ (i + 1) y.1 = d B ρB i x → Hdeg.mk ⟨w z, hw_cocy z⟩ = Hdeg.mk y`. Introduce `z x hx hψx y hy`. Rewrite using `[Hdeg_mk_eq_mk]`.

Take `⟨u, hu, hφu⟩` from `exists_mapC_eq hmid (sub_mem (hlift_mem z) hx) (by rw [map_sub, hlift, hψx]; exact sub_self _)`. Use `⟨u, hu, mapC_injective hinj (i + 1) ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mapC φ (i + 1) (d A ρA i u) = mapC φ (i + 1) (w z - y.1)`. Rewrite using `[mapC_d φ hφ, hφu, map_sub, map_sub, hw z, hy]`. Set `δ₀ : cocyDeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1)` to `{ toFun := fun z => Hdeg.mk ⟨w z, hw_cocy z⟩ map_add' := fun a b => by`.

Rewrite using `[← Hdeg_mk_add]`. Conclude with `key (a + b) (lift a + lift b) (Submodule.add_mem _ (hlift_mem a) (hlift_mem b)) (by rw [map_add, hlift, hlift]; rfl) (⟨w a, hw_cocy a⟩ + ⟨w b, hw_cocy b⟩) (by change mapC φ (i + 1) (w a + w b) = _; rw [map_add, map_add, hw, hw])`. Use the proof step `map_smul' := fun r a => by`. Rewrite using `[RingHom.id_apply, ← Hdeg_mk_smul]`. Conclude with `key (r • a) (r • lift a) (Submodule.smul_mem _ r (hlift_mem a)) (by rw [map_smul, hlift]; rfl) (r • ⟨w a, hw_cocy a⟩) (by change mapC φ (i + 1) (r • w a) = _; rw [map_smul, map_smul, hw]) }`.

Establish `hδ₀ : ∀ z, δ₀ z = Hdeg.mk ⟨w z, hw_cocy z⟩` using `fun _ => rfl`. Establish `hker : (bdryDeg C dC ρC i).comap (cocyDeg C dC ρC i).subtype ≤ LinearMap.ker δ₀`. Introduce `z hz`. Rewrite `hz` using `[Submodule.mem_comap]`. Take `⟨x, -, hx, hψx, hdx⟩` from `exists_bdryDeg_of_mem_bdryDeg hψ hsurj hρB hddB hz`.

Rewrite using `[LinearMap.mem_ker, hδ₀, key z x hx hψx 0 (by rw [hdx]; exact map_zero _)]`. Conclude with `Hdeg_mk_zero`. Set `δ : Hdeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1)` to `Submodule.liftQ _ δ₀ hker`. Establish `hδ : ∀ z, δ (Hdeg.mk z) = δ₀ z` using `fun _ => rfl`. Use `⟨δ, ?_, ?_⟩` and prove the remaining obligations.

Introduce `y`. Take `⟨z, rfl⟩` from `Hdeg_mk_surjective y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[hδ, hδ₀, Hdeg_mk_eq_zero]`.

Take `⟨u, hu, hdu⟩` from `h`. Express the relevant statement in the definitionally equal form `d A ρA i u = w z at hdu`. Establish `hxc : lift z - mapC φ i u ∈ cocyDeg B dB ρB i`. Use `⟨LinearMap.mem_ker.2 ?_, Submodule.sub_mem _ (hlift_mem z) (mapC_mem_Cdeg hφd hu)⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← mapC_d φ hφ, hdu, hw z, sub_self]`.

Use `⟨Hdeg.mk ⟨_, hxc⟩, mapHdeg_mk hψ hψd ⟨_, hxc⟩ z ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mapC ψ i (lift z - mapC φ i u) = z.1`. Rewrite using `[map_sub, hlift, mapC_mapC_eq_zero hcomp, sub_zero]`. Introduce and unpack `⟨y, hy⟩`. Take `⟨x, rfl⟩` from `Hdeg_mk_surjective y`.

Rewrite using `[← hy, mapHdeg_mk hψ hψd x ⟨_, mapC_mem_cocyDeg hψ hψd x.2⟩ rfl, hδ, hδ₀, key _ x.1 x.2.2 rfl 0 (by rw [LinearMap.mem_ker.1 x.2.1]; exact map_zero _)]`. Conclude with `Hdeg_mk_zero`. Introduce `x`. Take `⟨y, rfl⟩` from `Hdeg_mk_surjective x`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite `h` using `[mapHdeg_mk hφ hφd y ⟨_, mapC_mem_cocyDeg hφ hφd y.2⟩ rfl, Hdeg_mk_eq_zero]`. Express the relevant statement in the definitionally equal form `mapC φ (i + 1) y.1 ∈ bdryDeg B dB ρB (i + 1) at h`. Take `⟨x, hx, hxy⟩` from `h`. Establish `hz : mapC ψ i x ∈ cocyDeg C dC ρC i` using `⟨LinearMap.mem_ker.2 (by rw [← mapC_d ψ hψ, hxy, mapC_mapC_eq_zero hcomp]), mapC_mem_Cdeg hψd hx⟩`.

Use `⟨Hdeg.mk ⟨_, hz⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hδ, hδ₀]`. Conclude with `key _ x hx rfl y hxy.symm`. Introduce and unpack `⟨x, hx⟩`. Take `⟨z, rfl⟩` from `Hdeg_mk_surjective x`.

Rewrite using `[← hx, hδ, hδ₀, mapHdeg_mk hφ hφd ⟨w z, hw_cocy z⟩ ⟨_, mapC_mem_cocyDeg hφ hφd (hw_cocy z)⟩ rfl, Hdeg_mk_eq_zero]`. Express the relevant statement in the definitionally equal form `mapC φ (i + 1) (w z) ∈ bdryDeg B dB ρB (i + 1)`. Rewrite using `[hw z]`. Conclude with `⟨lift z, hlift_mem z, rfl⟩`.
-/
theorem longExact (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hψ : ∀ I J h m, ψ J (ρB I J h m) = ρC I J h (ψ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) (hψd : ∀ I m, m ∈ dB I → ψ I m ∈ dC I)
    (hinj : ∀ I, Function.Injective (φ I)) (hcomp : ∀ I x, ψ I (φ I x) = 0)
    (hmid : ∀ I, ∀ x ∈ dB I, ψ I x = 0 → ∃ y ∈ dA I, φ I y = x)
    (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z)
    (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J)
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) :
    Function.Injective (mapHdeg dA dB φ hφ hφd 0) ∧
      ∀ i : ℕ, Function.Exact (mapHdeg dA dB φ hφ hφd i) (mapHdeg dB dC ψ hψ hψd i) ∧
        ∃ δ : Hdeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1),
          Function.Exact (mapHdeg dB dC ψ hψ hψd i) δ ∧ Function.Exact δ (mapHdeg dA dB φ hφ hφd (i + 1)) := by
  refine ⟨?_, fun i => ⟨exact_mapHdeg hφ hψ hφd hψd hinj hcomp hmid hsurj hρB hddB i, ?_⟩⟩
  · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    obtain ⟨z, rfl⟩ := Hdeg_mk_surjective y
    rw [mapHdeg_mk hφ hφd z ⟨_, mapC_mem_cocyDeg hφ hφd z.2⟩ rfl, Hdeg_mk_eq_zero] at hy
    have h0 : mapC φ 0 z.1 ∈ (⊥ : Submodule R (Cochain B 0)) := hy
    rw [Submodule.mem_bot, ← map_zero (mapC φ 0)] at h0
    have hz : z = 0 := Subtype.ext (mapC_injective hinj 0 h0)
    rw [hz, Hdeg_mk_zero]

  choose lift hlift_mem hlift using fun z : cocyDeg C dC ρC i => exists_mapC_eq_of_mem hsurj z.2.2
  choose w hw_mem hw using fun z : cocyDeg C dC ρC i =>
    exists_mapC_eq hmid (d_mem_Cdeg hρB (hlift_mem z))
      (by rw [mapC_d ψ hψ, hlift]; exact LinearMap.mem_ker.1 z.2.1)
  have hw_cocy : ∀ z, w z ∈ cocyDeg A dA ρA (i + 1) := fun z =>
    ⟨LinearMap.mem_ker.2 (mapC_injective hinj (i + 1 + 1) (by
      rw [mapC_d φ hφ, hw, hddB, map_zero])), hw_mem z⟩

  have key : ∀ (z : cocyDeg C dC ρC i) (x : Cochain B i), x ∈ Cdeg B dB i → mapC ψ i x = z.1 →
      ∀ y : cocyDeg A dA ρA (i + 1), mapC φ (i + 1) y.1 = d B ρB i x →
        Hdeg.mk ⟨w z, hw_cocy z⟩ = Hdeg.mk y := by
    intro z x hx hψx y hy
    rw [Hdeg_mk_eq_mk]
    obtain ⟨u, hu, hφu⟩ := exists_mapC_eq hmid (sub_mem (hlift_mem z) hx)
      (by rw [map_sub, hlift, hψx]; exact sub_self _)
    refine ⟨u, hu, mapC_injective hinj (i + 1) ?_⟩
    change mapC φ (i + 1) (d A ρA i u) = mapC φ (i + 1) (w z - y.1)
    rw [mapC_d φ hφ, hφu, map_sub, map_sub, hw z, hy]
  let δ₀ : cocyDeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1) :=
    { toFun := fun z => Hdeg.mk ⟨w z, hw_cocy z⟩
      map_add' := fun a b => by
        rw [← Hdeg_mk_add]
        exact key (a + b) (lift a + lift b) (Submodule.add_mem _ (hlift_mem a) (hlift_mem b))
          (by rw [map_add, hlift, hlift]; rfl) (⟨w a, hw_cocy a⟩ + ⟨w b, hw_cocy b⟩)
          (by change mapC φ (i + 1) (w a + w b) = _; rw [map_add, map_add, hw, hw])
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← Hdeg_mk_smul]
        exact key (r • a) (r • lift a) (Submodule.smul_mem _ r (hlift_mem a))
          (by rw [map_smul, hlift]; rfl) (r • ⟨w a, hw_cocy a⟩)
          (by change mapC φ (i + 1) (r • w a) = _; rw [map_smul, map_smul, hw]) }
  have hδ₀ : ∀ z, δ₀ z = Hdeg.mk ⟨w z, hw_cocy z⟩ := fun _ => rfl
  have hker : (bdryDeg C dC ρC i).comap (cocyDeg C dC ρC i).subtype ≤ LinearMap.ker δ₀ := by
    intro z hz
    rw [Submodule.mem_comap] at hz
    obtain ⟨x, -, hx, hψx, hdx⟩ := exists_bdryDeg_of_mem_bdryDeg hψ hsurj hρB hddB hz
    rw [LinearMap.mem_ker, hδ₀, key z x hx hψx 0 (by rw [hdx]; exact map_zero _)]
    exact Hdeg_mk_zero
  let δ : Hdeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1) := Submodule.liftQ _ δ₀ hker
  have hδ : ∀ z, δ (Hdeg.mk z) = δ₀ z := fun _ => rfl
  refine ⟨δ, ?_, ?_⟩
  ·
    intro y
    obtain ⟨z, rfl⟩ := Hdeg_mk_surjective y
    constructor
    · intro h
      rw [hδ, hδ₀, Hdeg_mk_eq_zero] at h
      obtain ⟨u, hu, hdu⟩ := h
      change d A ρA i u = w z at hdu
      have hxc : lift z - mapC φ i u ∈ cocyDeg B dB ρB i := by
        refine ⟨LinearMap.mem_ker.2 ?_, Submodule.sub_mem _ (hlift_mem z) (mapC_mem_Cdeg hφd hu)⟩
        rw [map_sub, ← mapC_d φ hφ, hdu, hw z, sub_self]
      refine ⟨Hdeg.mk ⟨_, hxc⟩, mapHdeg_mk hψ hψd ⟨_, hxc⟩ z ?_⟩
      change mapC ψ i (lift z - mapC φ i u) = z.1
      rw [map_sub, hlift, mapC_mapC_eq_zero hcomp, sub_zero]
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := Hdeg_mk_surjective y
      rw [← hy, mapHdeg_mk hψ hψd x ⟨_, mapC_mem_cocyDeg hψ hψd x.2⟩ rfl, hδ, hδ₀,
        key _ x.1 x.2.2 rfl 0 (by rw [LinearMap.mem_ker.1 x.2.1]; exact map_zero _)]
      exact Hdeg_mk_zero
  ·
    intro x
    obtain ⟨y, rfl⟩ := Hdeg_mk_surjective x
    constructor
    · intro h
      rw [mapHdeg_mk hφ hφd y ⟨_, mapC_mem_cocyDeg hφ hφd y.2⟩ rfl, Hdeg_mk_eq_zero] at h
      change mapC φ (i + 1) y.1 ∈ bdryDeg B dB ρB (i + 1) at h
      obtain ⟨x, hx, hxy⟩ := h
      have hz : mapC ψ i x ∈ cocyDeg C dC ρC i :=
        ⟨LinearMap.mem_ker.2 (by rw [← mapC_d ψ hψ, hxy, mapC_mapC_eq_zero hcomp]),
          mapC_mem_Cdeg hψd hx⟩
      refine ⟨Hdeg.mk ⟨_, hz⟩, ?_⟩
      rw [hδ, hδ₀]
      exact key _ x hx rfl y hxy.symm
    · rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := Hdeg_mk_surjective x
      rw [← hx, hδ, hδ₀,
        mapHdeg_mk hφ hφd ⟨w z, hw_cocy z⟩ ⟨_, mapC_mem_cocyDeg hφ hφd (hw_cocy z)⟩ rfl,
        Hdeg_mk_eq_zero]
      change mapC φ (i + 1) (w z) ∈ bdryDeg B dB ρB (i + 1)
      rw [hw z]
      exact ⟨lift z, hlift_mem z, rfl⟩

end LongExact

end Cech

section Graded

universe w

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

/- English proof (translation)
Use `Submodule.span_induction (p := fun x _ => locResS I J h x ∈ degLoc 𝓜 c J) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hm, hs, hae, rfl⟩`. Conclude with `Submodule.subset_span ⟨m, ⟨s, monos_mono h s.2⟩, a, e, hm, hs, hae, locRes_mk h m s⟩`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Simplify using `using add_mem hx hy`. Introduce `r x _ hx`. Simplify using `using Submodule.smul_mem _ r hx`.
-/
theorem degLoc_locResS_mem (𝓜 : GradedPMod S N M) (c : ℤ) (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) : locResS I J h x ∈ degLoc 𝓜 c J := by
  refine Submodule.span_induction (p := fun x _ => locResS I J h x ∈ degLoc 𝓜 c J) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    exact Submodule.subset_span ⟨m, ⟨s, monos_mono h s.2⟩, a, e, hm, hs, hae, locRes_mk h m s⟩
  · simp
  · intro x y _ _ hx hy; simpa using add_mem hx hy
  · intro r x _ hx; simpa using Submodule.smul_mem _ r hx

/- English proof (translation)
Use `Submodule.span_induction (p := fun x _ => (locMap f.toLin I.1).restrictScalars S x ∈ degLoc 𝓜' c I) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hm, hs, hae, rfl⟩`. Conclude with `Submodule.subset_span ⟨f.toLin m, s, a, e, f.map_piece a m hm, hs, hae, locMap_mk f.toLin I.1 m s⟩`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Simplify using `using add_mem hx hy`. Introduce `r x _ hx`. Simplify using `using Submodule.smul_mem _ r hx`.
-/
theorem degLoc_locMap_mem {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜')
    (c : ℤ) (I : StdCell N) (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) :
    locMap f.toLin I.1 x ∈ degLoc 𝓜' c I := by
  refine Submodule.span_induction (p := fun x _ => (locMap f.toLin I.1).restrictScalars S x ∈
    degLoc 𝓜' c I) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    exact Submodule.subset_span ⟨f.toLin m, s, a, e, f.map_piece a m hm, hs, hae,
      locMap_mk f.toLin I.1 m s⟩
  · simp
  · intro x y _ _ hx hy; simpa using add_mem hx hy
  · intro r x _ hx; simpa using Submodule.smul_mem _ r hx

/- English proof (translation)
Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m s`. Express the relevant statement in the definitionally equal form `locMap f J.1 (locRes h _) = locRes h (locMap f I.1 _)`. Rewrite using `[locRes_mk, locMap_mk, locMap_mk, locRes_mk]`.
-/
theorem locMap_comp_locResS (f : M →ₗ[Poly S N] M') (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) : locMap f J.1 (locResS I J h x) = locResS I J h (locMap f I.1 x) := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locMap f J.1 (locRes h _) = locRes h (locMap f I.1 _)
    rw [locRes_mk, locMap_mk, locMap_mk, locRes_mk]

omit [Module S M] [IsScalarTower S (Poly S N) M] [Module S M'] [IsScalarTower S (Poly S N) M'] in

/- English proof (translation)
Unfold `locMap`. Conclude with `IsLocalizedModule.map_injective (S := monos (S := S) I) (f := LocalizedModule.mkLinearMap (monos (S := S) I) M) (g := LocalizedModule.mkLinearMap (monos (S := S) I) M') (h_inj := hf)`.
-/
theorem locMap_injective (f : M →ₗ[Poly S N] M') (hf : Function.Injective f)
    (I : Finset (Fin (N + 1))) : Function.Injective (locMap f I) :=
  by
    unfold locMap
    exact IsLocalizedModule.map_injective (S := monos (S := S) I)
      (f := LocalizedModule.mkLinearMap (monos (S := S) I) M)
      (g := LocalizedModule.mkLinearMap (monos (S := S) I) M') (h_inj := hf)

variable {M'' : Type w} [AddCommGroup M''] [Module (Poly S N) M''] [Module S M'']
  [IsScalarTower S (Poly S N) M'']

/- English proof (translation)
Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m s`. Rewrite using `[locMap_mk, locMap_mk, hfg]`. Conclude with `LocalizedModule.zero_mk s`.
-/
theorem locMap_locMap_eq_zero (f : M' →ₗ[Poly S N] M) (g : M →ₗ[Poly S N] M'')
    (hfg : ∀ m, g (f m) = 0) (I : Finset (Fin (N + 1))) (x : LocMod S N M' I) :
    locMap g I (locMap f I x) = 0 := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [locMap_mk, locMap_mk, hfg]
    exact LocalizedModule.zero_mk s

end Graded

/- English proof (translation)
Introduce `S _ _ N M' M M'' _ _ _ _ _ _ _ _ _ _ _ _ 𝓜' 𝓜 𝓜'' f g hf hg hfg c`. Establish `hex` using `hdeg S N M' M M'' 𝓜' 𝓜 𝓜'' f g hf hg hfg c`. Conclude with `Cech.longExact (A := locSys S N M') (B := locSys S N M) (C := locSys S N M'') (ρA := locResS) (ρB := locResS) (ρC := locResS) (dA := degLoc 𝓜' c) (dB := degLoc 𝓜 c) (dC := degLoc 𝓜'' c) (φ := fun I => (locMap f.toLin I.1).restrictScalars S) (ψ := fun I => (locMap g.toLin I.1).res …`.
-/
theorem CechExact.proof (hdsq : CechDSq.Statement.{u, max u v}) (hdeg : DegLocExact.Statement.{u, v}) :
    CechExact.Statement.{u, v} := by
  intro S _ _ N M' M M'' _ _ _ _ _ _ _ _ _ _ _ _ 𝓜' 𝓜 𝓜'' f g hf hg hfg c
  have hex := hdeg S N M' M M'' 𝓜' 𝓜 𝓜'' f g hf hg hfg c
  exact Cech.longExact (A := locSys S N M') (B := locSys S N M) (C := locSys S N M'')
    (ρA := locResS) (ρB := locResS) (ρC := locResS)
    (dA := degLoc 𝓜' c) (dB := degLoc 𝓜 c) (dC := degLoc 𝓜'' c)
    (φ := fun I => (locMap f.toLin I.1).restrictScalars S)
    (ψ := fun I => (locMap g.toLin I.1).restrictScalars S)
    (fun I J h x => locMap_comp_locResS f.toLin I J h x) (fun I J h x => locMap_comp_locResS g.toLin I J h x)
    (fun I x hx => degLoc_locMap_mem f c I x hx) (fun I x hx => degLoc_locMap_mem g c I x hx)
    (fun I => locMap_injective f.toLin hf I.1)
    (fun I x => locMap_locMap_eq_zero f.toLin g.toLin (fun m => hfg.apply_apply_eq_zero m) I.1 x)
    (fun I => (hex I).1) (fun I => (hex I).2)
    (fun I J h x hx => degLoc_locResS_mem 𝓜 c I J h x hx)
    (hdsq _ Finset.univ S (locSys S N M) locResS locResS_comp)

end

end GroundTheory.Heights₂.Heights.Kleiman
