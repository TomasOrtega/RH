import Mathlib
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot
import ReciprocityTheory.GroupCohomology.PartialProdCoe

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

section Alg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)

def IsTwoCocycle (c : G → G → A) : Prop := ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0

def D1 (y : G → A) (g h : G) : A := ρ g (y h) - y (g * h) + y g

variable {ρ}

/- English proof (translation)
Introduce `g h k`. Establish `h1` using `hc g h k`. Establish `h2` using `hc' g h k`. Simplify using `only [map_sub]`. Take the linear combination `(norm := abel) h1 - h2`.
-/
theorem IsTwoCocycle.sub {c c' : G → G → A} (hc : IsTwoCocycle ρ c) (hc' : IsTwoCocycle ρ c') :
    IsTwoCocycle ρ (fun g h => c g h - c' g h) := by
  intro g h k
  have h1 := hc g h k
  have h2 := hc' g h k
  simp only [map_sub]
  linear_combination (norm := abel) h1 - h2

variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)

include hrs hr in
/- English proof (translation)
Establish `h : s n = (r n)⁻¹ * n` using `by rw [eq_inv_mul_iff_mul_eq, hrs]`. Rewrite using `[h]`. Conclude with `N.mul_mem (N.inv_mem (hr n)) hn`.
-/
theorem s_mem {n : G} (hn : n ∈ N) : s n ∈ N := by
  have h : s n = (r n)⁻¹ * n := by rw [eq_inv_mul_iff_mul_eq, hrs]
  rw [h]; exact N.mul_mem (N.inv_mem (hr n)) hn

include hc hrs hr hrn hsn in

/- English proof (translation)
Establish `h1` using `hc n (r g) (s g)`. Rewrite `h1` using `[hrs, h0 n hn _ (hr g)]`. Simplify using `only [D1]`. Rewrite using `[hrn n hn, hsn n hn, h0 _ (hr n) _ (s_mem hrs hr hn), map_neg]`. Take the linear combination `(norm := abel) h1`.
-/
theorem stepA (h0 : ∀ n ∈ N, ∀ m ∈ N, c n m = 0) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => - c (r x) (s x)) n g = 0 := by
  have h1 := hc n (r g) (s g)
  rw [hrs, h0 n hn _ (hr g)] at h1
  simp only [D1]
  rw [hrn n hn, hsn n hn, h0 _ (hr n) _ (s_mem hrs hr hn), map_neg]
  linear_combination (norm := abel) h1

include hc in
/- English proof (translation)
Establish `h1` using `hc n g h`. Rewrite `h1` using `[h0 n hn, h0 n hn]`. Take the linear combination `(norm := abel) - h1`.
-/
theorem mul_left_of_zero (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (n : G) (hn : n ∈ N) (g h : G) :
    c (n * g) h = ρ n (c g h) := by
  have h1 := hc n g h
  rw [h0 n hn, h0 n hn] at h1
  linear_combination (norm := abel) - h1

include hc in
/- English proof (translation)
Establish `h1` using `hc g m k`. Establish `h2` using `mul_left_of_zero hc h0 (g * m * g⁻¹) (Subgroup.Normal.conj_mem ‹_› m hm g) g k`. Rewrite `h2` using `[inv_mul_cancel_right]`. Rewrite `h1` using `[h0 m hm, map_zero, h2]`. Take the linear combination `(norm := abel) h1`.
-/
theorem theta_mul [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (g m : G) (hm : m ∈ N) (k : G) :
    c g (m * k) = c g m + ρ (g * m * g⁻¹) (c g k) := by
  have h1 := hc g m k
  have h2 := mul_left_of_zero hc h0 (g * m * g⁻¹) (Subgroup.Normal.conj_mem ‹_› m hm g) g k
  rw [inv_mul_cancel_right] at h2
  rw [h0 m hm, map_zero, h2] at h1
  linear_combination (norm := abel) h1

include hc hrs hr hrn hsn in

/- English proof (translation)
Establish `ha0 : ρ (r n) (e (s n)) = 0` using `by rw [he0 _ (s_mem hrs hr hn), map_zero]`. Prove the components needed by the constructor for the conclusion. Simplify using `only [D1]`. Rewrite using `[hrn n hn, hsn n hn, ha0, h0 n hn, map_mul, Module.End.mul_apply]`. Normalize the expressions using the abelian group laws.

Simplify using `only [D1]`. Establish `hconj : g * n * g⁻¹ ∈ N` using `Subgroup.Normal.conj_mem ‹_› n hn g`. Establish `h1 : g * n = (g * n * g⁻¹) * g` using `by group`. Establish `h2 : c g n = ρ (r g) (e (s g)) - ρ (g * n * g⁻¹) (ρ (r g) (e (s g)))`. Establish `h3 : c g n = ρ (r g) (c (s g) n)` using `by conv_lhs => rw [← hrs g]`.

Conclude with `mul_left_of_zero hc h0 _ (hr g) _ _`. Establish `h4` using `he (s g) (s g * n * (s g)⁻¹) (Subgroup.Normal.conj_mem ‹_› n hn _)`. Establish `h5 : (s g)⁻¹ * (s g * n * (s g)⁻¹) * s g = n` using `by group`. Rewrite `h4` using `[h5]`. Rewrite using `[h3, h4, map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`.

Establish `key : ∀ a b : G, a * (b * n * b⁻¹) = (a * b) * n * (a * b)⁻¹ * a` using `by intros; group`. Establish `key'` using `key (r g) (s g)`. Rewrite `key'` using `[hrs]`. Rewrite using `[key']`. Rewrite using `[ha0, map_zero, h1, hrn _ hconj, hsn _ hconj, h2, map_mul ρ (g * n * g⁻¹) (r g), Module.End.mul_apply]`.

Normalize the expressions using the abelian group laws.
-/
theorem stepB [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (e : G → A) (he0 : ∀ g ∈ N, e g = 0)
    (he : ∀ g, ∀ n ∈ N, c g (g⁻¹ * n * g) = e g - ρ n (e g)) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => ρ (r x) (e (s x))) n g = 0 ∧ c g n - D1 ρ (fun x => ρ (r x) (e (s x))) g n = 0 := by
  have ha0 : ρ (r n) (e (s n)) = 0 := by rw [he0 _ (s_mem hrs hr hn), map_zero]
  constructor
  · simp only [D1]
    rw [hrn n hn, hsn n hn, ha0, h0 n hn, map_mul, Module.End.mul_apply]
    abel
  · simp only [D1]
    have hconj : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹_› n hn g
    have h1 : g * n = (g * n * g⁻¹) * g := by group
    have h2 : c g n = ρ (r g) (e (s g)) - ρ (g * n * g⁻¹) (ρ (r g) (e (s g))) := by
      have h3 : c g n = ρ (r g) (c (s g) n) := by
        conv_lhs => rw [← hrs g]
        exact mul_left_of_zero hc h0 _ (hr g) _ _
      have h4 := he (s g) (s g * n * (s g)⁻¹) (Subgroup.Normal.conj_mem ‹_› n hn _)
      have h5 : (s g)⁻¹ * (s g * n * (s g)⁻¹) * s g = n := by group
      rw [h5] at h4
      rw [h3, h4, map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      have key : ∀ a b : G, a * (b * n * b⁻¹) = (a * b) * n * (a * b)⁻¹ * a := by intros; group
      have key' := key (r g) (s g)
      rw [hrs] at key'
      rw [key']
    rw [ha0, map_zero, h1, hrn _ hconj, hsn _ hconj, h2, map_mul ρ (g * n * g⁻¹) (r g), Module.End.mul_apply]
    abel

include hc in

/- English proof (translation)
Establish `hR : ∀ g h n, n ∈ N → c g (h * n) = c g h` using `fun g h n hn => by`. Establish `h1` using `hc g h n`. Rewrite `h1` using `[h0' n hn, h0' n hn, map_zero]`. Take the linear combination `(norm := abel) h1`. Establish `hL : ∀ g h n, n ∈ N → c g (n * h) = c g h` using `fun g h n hn => by`.

Establish `: n * h = h * (h⁻¹ * n * h)` using `by group`. Rewrite using `[this, hR _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn h)]`. Establish `hM : ∀ g h n, n ∈ N → c (g * n) h = c g h` using `fun g h n hn => by`. Establish `h1` using `hc g n h`. Rewrite `h1` using `[h0 n hn, h0' n hn, map_zero, hL _ _ _ hn]`.

Take the linear combination `(norm := abel) - h1`. Use `⟨hR g h n hn, hM g h n hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_left_of_zero hc h0 n hn]`. Establish `: n * g = g * (g⁻¹ * n * g)` using `by group`. Rewrite using `[this, hM _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn g)]`.
-/
theorem stepC [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (h0' : ∀ n ∈ N, ∀ g, c g n = 0) (n : G) (hn : n ∈ N)
    (g h : G) : c g (h * n) = c g h ∧ c (g * n) h = c g h ∧ ρ n (c g h) = c g h := by
  have hR : ∀ g h n, n ∈ N → c g (h * n) = c g h := fun g h n hn => by
    have h1 := hc g h n
    rw [h0' n hn, h0' n hn, map_zero] at h1
    linear_combination (norm := abel) h1
  have hL : ∀ g h n, n ∈ N → c g (n * h) = c g h := fun g h n hn => by
    have : n * h = h * (h⁻¹ * n * h) := by group
    rw [this, hR _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn h)]
  have hM : ∀ g h n, n ∈ N → c (g * n) h = c g h := fun g h n hn => by
    have h1 := hc g n h
    rw [h0 n hn, h0' n hn, map_zero, hL _ _ _ hn] at h1
    linear_combination (norm := abel) - h1
  refine ⟨hR g h n hn, hM g h n hn, ?_⟩
  rw [← mul_left_of_zero hc h0 n hn]
  have : n * g = g * (g⁻¹ * n * g) := by group
  rw [this, hM _ _ _ (Subgroup.Normal.conj_mem' ‹_› n hn g)]

end Alg

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
