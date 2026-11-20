import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinatesModPrimeSelfDualStabilizerStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TypeFrameCover

open GlobalTheory.LevDesc

section Primes

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

/- English proof (translation)
Use `halfPrime_isPrime l v.2.1.isMaximal ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `g_dvd (D := D) v.1`. Rewrite using `[hM, hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ v.2.2`.
-/
theorem typePrime_isPrime {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (v : Sq D.host) :
    (typePrime l v).IsPrime := by
  refine halfPrime_isPrime l v.2.1.isMaximal ?_
  obtain ⟨k, hk⟩ := g_dvd (D := D) v.1
  rw [hM, hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ v.2.2

/- English proof (translation)
Take `⟨hP, hN⟩` from `hl₂.typePrime_spec v`. Establish `hne : typePrime l₂ v ≠ ⊥`. Introduce `h`. Rewrite `hN` using `[h, Ideal.absNorm_bot]`. Conclude with `(D.host.g_prime v.1).ne_zero hN.symm`.

Conclude with `(hP.isMaximal hne).eq_of_le (typePrime_isPrime hM v).ne_top (sup_le_sup_right hle _)`.
-/
theorem typePrime_eq {l l₂ : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (hl₂ : IsTypeLevel l₂)
    (hle : l₂.Mb ≤ l.Mb) (v : Sq D.host) : typePrime l₂ v = typePrime l v := by
  obtain ⟨hP, hN⟩ := hl₂.typePrime_spec v
  have hne : typePrime l₂ v ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hN
    exact (D.host.g_prime v.1).ne_zero hN.symm
  exact (hP.isMaximal hne).eq_of_le (typePrime_isPrime hM v).ne_top (sup_le_sup_right hle _)

/- English proof (translation)
Establish `hP` using `typePrime_isPrime hM v`. Establish `h1 : ∏ PP ∈ Pg, PP.asIdeal ≤ typePrime l v` using `hMb ▸ le_sup_left`. Take `⟨PP, hPP, h2⟩` from `(hP.prod_le).1 h1`. Conclude with `⟨PP, hPP, PP.isMaximal.eq_of_le hP.ne_top h2⟩`.
-/
theorem exists_mem_eq {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) (v : Sq D.host) : ∃ PP ∈ Pg, PP.asIdeal = typePrime l v := by
  have hP := typePrime_isPrime hM v
  have h1 : ∏ PP ∈ Pg, PP.asIdeal ≤ typePrime l v := hMb ▸ le_sup_left
  obtain ⟨PP, hPP, h2⟩ := (hP.prod_le).1 h1
  exact ⟨PP, hPP, PP.isMaximal.eq_of_le hP.ne_top h2⟩

/- English proof (translation)
Use `choose f hf hfe using exists_mem_eq hM hMb`. Establish `hinj : Function.Injective (fun v ↦ (⟨f v, hf v⟩ : Pg))`. Introduce `v w h`. Establish `h' : typePrime l v = typePrime l w`. Rewrite using `[← hfe v, ← hfe w]`.

Conclude with `congrArg (fun x : Pg ↦ x.1.asIdeal) h`. Assume the negation of the conclusion as `hvw`. Establish `hc` using `typePrime_coprime (l := l) hvw`. Rewrite `hc` using `[Function.onFun, Ideal.isCoprime_iff_sup_eq, h', sup_idem]`. Conclude with `(typePrime_isPrime hM w).ne_top hc`.

Establish `hsurj : Function.Surjective (fun v ↦ (⟨f v, hf v⟩ : Pg))`. Introduce and unpack `⟨PP, hPP⟩`. Establish `hle : l.Mb ≤ PP.asIdeal` using `hMb ▸ Ideal.prod_le_inf.trans (Finset.inf_le hPP)`. Establish `hm : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`. Rewrite using `[← Nat.cast_mul, ← hM]`.

Conclude with `hle (natCast_M_mem l)`. Establish `hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`. Break down `PP.isPrime.mem_or_mem hm with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`.

Take `⟨k, hk⟩` from `hk`. Establish `hg : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hk`. Set `w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)` to `⟨Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal, inferInstance, fun e ↦ by`.

Rewrite `hg` using `[e, Ideal.mem_bot]`. Conclude with `(D.host.g_prime k).ne_zero (by exact_mod_cast hg)⟩`. Establish `he : typePrime l ⟨k, ⟨w, hg⟩⟩ = PP.asIdeal` using `halfPrime_eq l w.isMaximal PP.isPrime (sup_le hle Ideal.map_comap_le)`. Use `⟨⟨k, ⟨w, hg⟩⟩, Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)⟩` and prove the remaining obligations. Conclude with `(hfe _).trans he`.

Conclude with `⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun v ↦ hfe v⟩`.
-/
theorem exists_equiv {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) : ∃ e : Sq D.host ≃ Pg, ∀ v, (e v).1.asIdeal = typePrime l v := by
  choose f hf hfe using exists_mem_eq hM hMb
  have hinj : Function.Injective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    intro v w h
    have h' : typePrime l v = typePrime l w := by
      rw [← hfe v, ← hfe w]; exact congrArg (fun x : Pg ↦ x.1.asIdeal) h
    by_contra hvw
    have hc := typePrime_coprime (l := l) hvw
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq, h', sup_idem] at hc
    exact (typePrime_isPrime hM w).ne_top hc
  have hsurj : Function.Surjective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    rintro ⟨PP, hPP⟩
    have hle : l.Mb ≤ PP.asIdeal := hMb ▸ Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    have hm : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Nat.cast_mul, ← hM]; exact hle (natCast_M_mem l)
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rcases PP.isPrime.mem_or_mem hm with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal := by
      rw [Ideal.mem_comap, map_natCast]; exact hk
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) :=
      ⟨Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal, inferInstance, fun e ↦ by
        rw [e, Ideal.mem_bot] at hg
        exact (D.host.g_prime k).ne_zero (by exact_mod_cast hg)⟩
    have he : typePrime l ⟨k, ⟨w, hg⟩⟩ = PP.asIdeal :=
      halfPrime_eq l w.isMaximal PP.isPrime (sup_le hle Ideal.map_comap_le)
    refine ⟨⟨k, ⟨w, hg⟩⟩, Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)⟩
    exact (hfe _).trans he
  exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun v ↦ hfe v⟩

/- English proof (translation)
Establish `hc : Nat.card (kP PP) = D.host.g v.1`. Rewrite using `[← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)`. Use `haveI := Fintype.ofFinite (kP PP)`. Conclude with `⟨ZMod.ringEquivOfPrime (kP PP) (D.host.g_prime v.1) (by rw [← Nat.card_eq_fintype_card, hc])⟩`.
-/
theorem nonempty_iso {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (v : Sq D.host) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hPP : PP.asIdeal = typePrime l₂ v) : Nonempty (ZMod (D.host.g v.1) ≃+* kP PP) := by
  have hc : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Fintype.ofFinite (kP PP)
  exact ⟨ZMod.ringEquivOfPrime (kP PP) (D.host.g_prime v.1) (by rw [← Nat.card_eq_fintype_card, hc])⟩

end Primes

section Frame

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hker : typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ≤ LinearMap.ker φ`. Rewrite using `[← hPP, Submodule.smul_le]`. Introduce `a ha x _`. Rewrite using `[LinearMap.mem_ker, map_smul]`.

Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]`. Set `ψ` to `(typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).liftQ φ hker`. Establish `hψs : Function.Surjective ψ`. Introduce `y`.

Take `⟨x, rfl⟩` from `hφ y`. Conclude with `⟨Submodule.Quotient.mk x, rfl⟩`. Establish `hc : Nat.card (𝓞 D.host.E ⧸ typePrime l₂ v) = D.host.g v.1`. Rewrite using `[← (hl₂.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 D.host.E ⧸ typePrime l₂ v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)`.

Use `haveI := Dw.fin`. Use `haveI := Dw.proj`. Establish `hN : Nat.card (QMod Dw.La (typePrime l₂ v)) = D.host.g v.1 ^ D.R.r`. Rewrite using `[GlobalTheory.natCard_quot_smul_top_of_projective, hc, Dw.rank, hr]`. Establish `hc' : Nat.card (kP PP) = D.host.g v.1`.

Rewrite using `[← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hN' : Nat.card (Fin D.R.r → kP PP) = D.host.g v.1 ^ D.R.r`. Rewrite using `[Nat.card_fun, hc', Nat.card_eq_fintype_card, Fintype.card_fin]`. Use `haveI : Finite (QMod Dw.La (typePrime l₂ v)) := Nat.finite_of_card_ne_zero (by rw [hN]; exact pow_ne_zero _ (D.host.g_prime _).ne_zero)`. Establish `hψb : Function.Bijective ψ` using `hψs.bijective_of_nat_card_le (by rw [hN, hN'])`.

Set `e1 : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → kP PP)` to `AddEquiv.ofBijective ψ.toAddMonoidHom hψb`. Set `e2 : (Fin D.R.r → kP PP) ≃+ (Fin D.R.r → ZMod (D.host.g v.1))` to `AddEquiv.piCongrRight (fun _ ↦ iso.symm.toAddEquiv)`. Conclude with `⟨e1.trans e2, fun x ↦ rfl⟩`.
-/
theorem exists_frame {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (hr : Dw.p + Dw.q = D.R.r) (v : Sq D.host)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP.asIdeal = typePrime l₂ v) (iso : ZMod (D.host.g v.1) ≃+* kP PP)
    {n : ℕ} (hn : n = D.R.r) (φ : Dw.La →ₗ[𝓞 D.host.E] (Fin n → kP PP)) (hφ : Function.Surjective φ) :
    ∃ f : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)),
      ∀ x : Dw.La, f (Submodule.Quotient.mk x) = fun j ↦ iso.symm (φ x (Fin.cast hn.symm j)) := by
  subst hn
  have hker : typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ≤ LinearMap.ker φ := by
    rw [← hPP, Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let ψ := (typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).liftQ φ hker
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l₂ v) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l₂ v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Dw.fin
  haveI := Dw.proj
  have hN : Nat.card (QMod Dw.La (typePrime l₂ v)) = D.host.g v.1 ^ D.R.r := by
    rw [GlobalTheory.natCard_quot_smul_top_of_projective, hc, Dw.rank, hr]
  have hc' : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN' : Nat.card (Fin D.R.r → kP PP) = D.host.g v.1 ^ D.R.r := by
    rw [Nat.card_fun, hc', Nat.card_eq_fintype_card, Fintype.card_fin]
  haveI : Finite (QMod Dw.La (typePrime l₂ v)) :=
    Nat.finite_of_card_ne_zero (by rw [hN]; exact pow_ne_zero _ (D.host.g_prime _).ne_zero)
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le (by rw [hN, hN'])
  let e1 : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → kP PP) := AddEquiv.ofBijective ψ.toAddMonoidHom hψb
  let e2 : (Fin D.R.r → kP PP) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)) :=
    AddEquiv.piCongrRight (fun _ ↦ iso.symm.toAddEquiv)
  exact ⟨e1.trans e2, fun x ↦ rfl⟩

end Frame

section Main

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hyz`.
-/
theorem mulVec_reindex {K : Type} [CommRing K] {n r : ℕ} (h : n = r) (hr : r ≤ n) (Mn : Matrix (Fin n) (Fin n) K)
    (y z : Fin n → K)
    (hyz : (fun j ↦ y (Fin.cast h.symm j)) = Mn.submatrix (Fin.castLE hr) (Fin.castLE hr) *ᵥ fun j ↦ z (Fin.cast h.symm j)) :
    y = Mn *ᵥ z := by
  subst h
  exact hyz

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R i hβ H Dw l l₂ ι hι hr hA hM hl₂ hle hMb lev hlev`. Take `⟨e, he⟩` from `exists_equiv hM hMb`. Establish `htp : ∀ v, typePrime l₂ v = typePrime l v` using `typePrime_eq hM hl₂ hle`. Establish `he₂ : ∀ v, (e v).1.asIdeal = typePrime l₂ v` using `fun v ↦ (he v).trans (htp v).symm`. Set `iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1` to `fun v ↦ (nonempty_iso hl₂ v _ (he₂ v)).some`.

Establish `hφ` using `fun v : Sq D.host ↦ GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) (R.βW i) (R.ΛW i) hβ Dw.La ι hι (e v).1`. Use `choose φ hφs hφk using hφ`. Establish `hfr0` using `fun v ↦ exists_frame hl₂ hr v (e v).1 (he₂ v) (iso v) (rank_Wc i) (φ v) (hφs v)`. Use `choose fr hfr using hfr0`. Use `⟨fr, e, iso, ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ g hg a`. Take `⟨κ, hκ, hκa⟩` from `hlev g`. Establish `hSt : Lev.finE (Wc D i) κ ∈ St (R.βW i)` using `parLev_St hκ.2.1`. Establish `hin : ∀ v, l.Mb ≤ (e v).1.asIdeal` using `fun v ↦ by rw [he v]; exact le_sup_left`. Establish `hkill : ∀ v, ∀ u ∈ l.Mb, ∀ x : Dw.La, φ v (u • x) = 0`.

Introduce `v u hu x`. Rewrite using `[map_smul]`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 (hin v hu), zero_mul]`. Establish `hcop : l.Mb ⊔ Mfr l = ⊤` using `l.coprime`.

Take `⟨u, hu, w, hw, huw⟩` from `Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l)`. Establish `ha : a = u • a + w • a` using `by rw [← add_smul, huw, one_smul]`. Establish `hlevφ : ∀ v, φ v (lev g a) = (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)).1 *ᵥ φ v a`. Introduce `v`. Establish `h1` using `hφk v κ hSt l.M (hin v (natCast_M_mem l)) (w • a) (lev g (w • a)) (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))`.

Establish `h2 : φ v (w • a) = φ v a` using `by conv_rhs => rw [ha]`. Rewrite using `[map_add, hkill v u hu, zero_add]`. Establish `h3 : φ v (lev g a) = φ v (lev g (w • a))` using `by conv_lhs => rw [ha]`. Rewrite using `[map_add, map_add, map_smul, hkill v u hu, zero_add]`. Rewrite using `[h3, h1, h2]`.

Establish `hliftφ : ∀ v, φ v (liftLa γ a) = φ v (lev g a)`. Introduce `v`. Establish `hγa : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a)` using `(liftLa_spec γ a).symm`. Establish `h0 : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) *ᵥ fr v (Submodule.Quotient.mk a) = fr v (Submodule.Quotient.mk (liftLa γ a))`. Establish `h00` using `GlobalTheory.LevDesc.typeRed_mulVec fr γ v (Submodule.Quotient.mk a)`.

Rewrite `h00` using `[hγa]`. Conclude with `h00`. Rewrite `h0` using `[hfr, hfr]`. Establish `h1` using `GlobalTheory.LevelActionPinned.equiv_mulVec (iso v) (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) (fun j ↦ (iso v).symm (φ v a (Fin.cast (rank_Wc i).symm j)))`. Rewrite `h1` using `[h0]`.

Simplify using `only [RingEquiv.apply_symm_apply] at h1`. Establish `hT : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))).map (iso v) = (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ) : Matrix _ _ _).submatrix (Fin.castLE (R.datWp i R.triv).hr) (Fin.castLE (R.datWp i R.triv).hr)`. Establish `h5 : R.eG g (e v) = upperLeftBlock (R.datWp i R.triv).hr (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ))` using `(congrFun hκ.2.2 (e v)).symm`. Establish `h6` using `upper_block_val_submatrix (R.datWp i R.triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 (e v).2))`. Rewrite `h6` using `[← h5, hg v]`.

Conclude with `h6`. Rewrite `h1` using `[hT]`. Rewrite using `[hlevφ v]`. Conclude with `mulVec_reindex (rank_Wc i) _ _ _ _ h1`. Establish `hall : ∀ v, liftLa γ a - lev g a ∈ typePrime l v • (⊤ : Submodule (𝓞 D.host.E) Dw.La)`.

Introduce `v`. Establish `hx : φ v (liftLa γ a - lev g a) = 0` using `by rw [map_sub, sub_eq_zero, hliftφ v]`. Establish `h4 : fr v (Submodule.Quotient.mk (liftLa γ a - lev g a)) = 0`. Rewrite using `[hfr, hx]`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Establish `h5` using `(AddEquiv.map_eq_zero_iff (fr v)).1 h4`. Rewrite `h5` using `[Submodule.Quotient.mk_eq_zero, htp]`. Conclude with `h5`. Establish `h3` using `mem_iInf_smul_top (typePrime_coprime (l := l)) hall`.

Establish `hle' : ⨅ v, typePrime l v ≤ l.Mb` using `iInf_typePrime_le.trans (sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).2 (by rw [← hM]; exact natCast_M_mem l)))`. Conclude with `Submodule.smul_mono_left hle' h3`. Introduce `γ hγ`. Rewrite using `[typeRed_eq_one, mem_grpR_iff]`. Introduce `v q`.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Establish `h1 : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a)` using `(liftLa_spec γ a).symm`. Rewrite using `[h1, ← Submodule.Quotient.mk_sub]`. Establish `h2 : liftLa γ a - a ∈ typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La)` using `Submodule.smul_mono_left ((le_sup_left : l.Mb ≤ typePrime l v).trans (htp v).ge) (hγ a)`. Conclude with `map_mem_smul_top (l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ h2`.
-/
theorem typeFrame_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → Dw.p + Dw.q = D.R.r → l.A = 1 → l.M = D.host.g 0 * D.host.g 1 → IsTypeLevel l₂ → l₂.Mb ≤ l.Mb → l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La, LevIs R i ι l.M (Mfr l) lev → ∃ (fr : TypeFrame Dw l₂) (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), (∀ (γ : LevelAut Dw l₂) (g : G), (∀ v, R.eG g (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (typeRed fr γ v)) → CongMod l.Mb (liftLa γ) (lev g)) ∧ ∀ γ : LevelAut Dw l₂, CongMod l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hβ H Dw l l₂ ι hι hr hA hM hl₂ hle hMb lev hlev
  obtain ⟨e, he⟩ := exists_equiv hM hMb
  have htp : ∀ v, typePrime l₂ v = typePrime l v := typePrime_eq hM hl₂ hle
  have he₂ : ∀ v, (e v).1.asIdeal = typePrime l₂ v := fun v ↦ (he v).trans (htp v).symm
  let iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1 := fun v ↦ (nonempty_iso hl₂ v _ (he₂ v)).some
  have hφ := fun v : Sq D.host ↦ GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) (R.βW i) (R.ΛW i) hβ Dw.La ι hι (e v).1
  choose φ hφs hφk using hφ
  have hfr0 := fun v ↦ exists_frame hl₂ hr v (e v).1 (he₂ v) (iso v) (rank_Wc i) (φ v) (hφs v)
  choose fr hfr using hfr0
  refine ⟨fr, e, iso, ?_, ?_⟩
  · intro γ g hg a
    obtain ⟨κ, hκ, hκa⟩ := hlev g
    have hSt : Lev.finE (Wc D i) κ ∈ St (R.βW i) := parLev_St hκ.2.1
    have hin : ∀ v, l.Mb ≤ (e v).1.asIdeal := fun v ↦ by rw [he v]; exact le_sup_left
    have hkill : ∀ v, ∀ u ∈ l.Mb, ∀ x : Dw.La, φ v (u • x) = 0 := by
      intro v u hu x
      rw [map_smul]
      funext j
      rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 (hin v hu), zero_mul]
    have hcop : l.Mb ⊔ Mfr l = ⊤ := l.coprime
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l)
    have ha : a = u • a + w • a := by rw [← add_smul, huw, one_smul]
    have hlevφ : ∀ v, φ v (lev g a) = (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)).1 *ᵥ φ v a := by
      intro v
      have h1 := hφk v κ hSt l.M (hin v (natCast_M_mem l)) (w • a) (lev g (w • a))
        (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
      have h2 : φ v (w • a) = φ v a := by
        conv_rhs => rw [ha]
        rw [map_add, hkill v u hu, zero_add]
      have h3 : φ v (lev g a) = φ v (lev g (w • a)) := by
        conv_lhs => rw [ha]
        rw [map_add, map_add, map_smul, hkill v u hu, zero_add]
      rw [h3, h1, h2]
    have hliftφ : ∀ v, φ v (liftLa γ a) = φ v (lev g a) := by
      intro v
      have hγa : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
      have h0 : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) *ᵥ
          fr v (Submodule.Quotient.mk a) = fr v (Submodule.Quotient.mk (liftLa γ a)) := by
        have h00 := GlobalTheory.LevDesc.typeRed_mulVec fr γ v (Submodule.Quotient.mk a)
        rw [hγa] at h00
        exact h00
      rw [hfr, hfr] at h0
      have h1 := GlobalTheory.LevelActionPinned.equiv_mulVec (iso v)
        (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)))
        (fun j ↦ (iso v).symm (φ v a (Fin.cast (rank_Wc i).symm j)))
      rw [h0] at h1
      simp only [RingEquiv.apply_symm_apply] at h1
      have hT : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))).map (iso v) =
          (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ) : Matrix _ _ _).submatrix
            (Fin.castLE (R.datWp i R.triv).hr) (Fin.castLE (R.datWp i R.triv).hr) := by
        have h5 : R.eG g (e v) = upperLeftBlock (R.datWp i R.triv).hr (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)) :=
          (congrFun hκ.2.2 (e v)).symm
        have h6 := upper_block_val_submatrix (R.datWp i R.triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 (e v).2))
        rw [← h5, hg v] at h6
        exact h6
      rw [hT] at h1
      rw [hlevφ v]
      exact mulVec_reindex (rank_Wc i) _ _ _ _ h1
    have hall : ∀ v, liftLa γ a - lev g a ∈ typePrime l v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
      intro v
      have hx : φ v (liftLa γ a - lev g a) = 0 := by rw [map_sub, sub_eq_zero, hliftφ v]
      have h4 : fr v (Submodule.Quotient.mk (liftLa γ a - lev g a)) = 0 := by
        rw [hfr, hx]
        funext j
        simp
      have h5 := (AddEquiv.map_eq_zero_iff (fr v)).1 h4
      rw [Submodule.Quotient.mk_eq_zero, htp] at h5
      exact h5
    have h3 := mem_iInf_smul_top (typePrime_coprime (l := l)) hall
    have hle' : ⨅ v, typePrime l v ≤ l.Mb := iInf_typePrime_le.trans
      (sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).2 (by rw [← hM]; exact natCast_M_mem l)))
    exact Submodule.smul_mono_left hle' h3
  · intro γ hγ
    rw [typeRed_eq_one, mem_grpR_iff]
    intro v q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
    rw [h1, ← Submodule.Quotient.mk_sub]
    have h2 : liftLa γ a - a ∈ typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      Submodule.smul_mono_left ((le_sup_left : l.Mb ≤ typePrime l v).trans (htp v).ge) (hγ a)
    exact map_mem_smul_top (l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ h2

end Main

end GlobalTheory.TypeFrameCover
