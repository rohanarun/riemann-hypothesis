module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRapidDecayOneSimpleRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.Shift

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem natW_top (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    (lam.natW a : ℤ) = lam.w a - lam.w (Fin.last n) := by
  have h1 : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left (Nat.succ_pos n)]
    rfl
  have h2 := lam.anti (Fin.le_last a)
  unfold DomWeight.natW
  rw [h1]
  omega

theorem lamZ_lamN (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    lamZ (lamN lam) a = lam.w a - lam.w (Fin.last n) := by
  unfold lamZ
  split_ifs with h
  · exact natW_top lam a
  · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
    simp [this]

theorem lamN_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (lamN lam i : ℤ) = lam.w i.castSucc - lam.w (Fin.last n) := natW_top lam _

theorem nuNext_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (nuNext (lamN lam) i : ℤ) = lam.w i.succ - lam.w (Fin.last n) := by
  rw [← lamZ_lamN]
  unfold nuNext lamZ
  simp only [Fin.val_succ]
  split_ifs <;> rfl

theorem natW_low (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) (i : Fin n) :
    (sg.natW i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have hi := i.2
  have h0 : 0 < n := by omega
  have h1 : sg.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left h0]
    exact hE _ (by simp only; omega)
  have h2 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (by rw [Fin.le_def]; simp only; omega)
  rw [hE ⟨n - 1, by omega⟩ (by simp only; omega)] at h2
  unfold DomWeight.natW
  rw [h1]
  omega

theorem d0_eq (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) :
    Formalism.BranchingDeterminantCap.d0 (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) = GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero lam sg := by
  unfold Formalism.BranchingDeterminantCap.d0 GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [lamZ_lamN, natW_low hE]
  ring

theorem rename_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) :
    incl K n (initMinor K I hs) = initMinor K I (hs.trans (Nat.le_succ n)) := by
  unfold initMinor incl
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp

end GlobalTheory.BrCompare.Shift


open GlobalTheory.BrCompare.Shift in
theorem GlobalTheory.BrCompare.shifted_branching_list_character : ∀ (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) ∧ (∀ u ∈ bmList (lamN lam) sg.natW, u ∈ zList lam sg) ∧ ((zList lam sg).map (bmChi (lamN lam) fun s => ((lamN lam s - sg.natW s : ℕ) : ℤ))).prod = Formalism.L2.Col.Br.cBr rfl lam sg ∧ (∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s) ∧ ∀ (K : Type) [Field K], Formalism.L2.Col.Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) sg.natW) := by
  intro n lam sg hI hE
  have hb : ∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Formalism.L2.Col.Br.aBr rfl lam sg s).toNat = sg.natW s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  refine ⟨?_, ?_, ?_, hb, ?_⟩
  · intro i
    have := hI i
    simp only [lamZ_lamN, natW_low hE]
    omega
  · intro u hu
    simp only [bmList, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_erase, rset, d0_eq hE,
      Finset.mem_Icc] at hu
    simp only [lamZ_lamN, natW_low hE] at hu
    obtain ⟨i, -, v, ⟨h1, h2, h3⟩, rfl⟩ := hu
    simp only [zList, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_erase, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet, Finset.mem_Icc]
    exact ⟨v + lam.w (Fin.last n), ⟨by omega, by omega, by omega⟩, by ring⟩
  · unfold zList Formalism.L2.Col.Br.cBr
    rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_def, List.map_map, Finset.prod_map_toList]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold bmChi
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 := lamN_cast lam j
    have h2 := natW_low hE j
    have h3 := hI j
    simp only
    omega
  · intro K _
    unfold Formalism.L2.Col.Br.xiBr xiB
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
    congr 2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSixth
section
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace EntryDatum

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

theorem phiT_add {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG') (hd' : d'.Ok)
    (c : 𝓞 E) (hc : ∀ P ∈ ST, c ∈ P.asIdeal) (x z : HomE E a b)
    (hz : ∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) : phiT K d d' (x + c • z) = phiT K d d' x := by
  have key : ∀ (x z : HomE E a b), (∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y := by
    intro x z hz h P y hy
    obtain ⟨h1, h2⟩ := h P y hy
    have h3 := hz P.1 P.2 y hy
    have h4 : c • z y ∈ d'.at P.1 := Submodule.smul_mem _ c h3
    have e : (x + c • z) y = x y + c • z y := rfl
    rw [e]
    refine ⟨add_mem h1 h4, ?_⟩
    rw [hd'.f_add P _ h1 _ h4, hd'.f_smul P c _ h3, Ideal.Quotient.eq_zero_iff_mem.2 (hc P.1 P.2), zero_mul, add_zero, h2]
  have hiff : (∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := by
    refine ⟨fun h => ?_, key x z hz⟩
    have h' := key (x + c • z) (-z) (fun P hP y hy => neg_mem (hz P hP y hy)) h
    have e : x + c • z + c • (-z) = x := by rw [smul_neg, add_neg_cancel_right]
    rwa [e] at h'
  unfold phiT
  by_cases h : ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem phiT_support {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) (hx : phiT K d d' x ≠ 0) : ∀ P ∈ ST, ∀ y ∈ d.at P, x y ∈ d'.at P := by
  intro P hP y hy
  unfold phiT at hx
  split_ifs at hx with h
  · exact (h ⟨P, hP⟩ y hy).1
  · exact absurd rfl hx

theorem norm_phiT_le {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (σ : K →+* ℂ) (x : HomE E a b) : ‖σ (phiT K d d' x)‖ ≤ 1 := by
  unfold phiT
  split_ifs <;> simp

theorem inFr_maps_iff (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    {M M₀ : Submodule (𝓞 E) (Sp E a)} {M' M₀' : Submodule (𝓞 E) (Sp E b)}
    (hf : ∀ x, f x ∈ M ↔ x ∈ M₀) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ M₀') (x : HomE E a b) :
    (∀ y ∈ M₀, inFr f f' x y ∈ M₀') ↔ ∀ y ∈ M, x y ∈ M' := by
  have e : ∀ y, f' (inFr f f' x y) = x (f y) := fun y => by simp [inFr]
  constructor
  · intro h y hy
    have h1 : f.symm y ∈ M₀ := (hf _).1 (by simpa using hy)
    have h2 := (hf' _).2 (h _ h1)
    rw [e] at h2
    simpa using h2
  · intro h y hy
    rw [← hf', e]
    exact h _ ((hf y).2 hy)

theorem inFr_add_smul (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x z : HomE E a b) (q k : ℕ) :
    inFr f f' (x + ((q * k : ℕ) : 𝓞 E) • z) = inFr f f' x + (q : E) • inFr f f' ((k : 𝓞 E) • z) := by
  have e : ∀ n : ℕ, ((n : ℕ) : 𝓞 E) • z = (n : E) • z := fun n => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [e, e]
  refine LinearMap.ext fun y => ?_
  simp [inFr, mul_smul]

theorem smallDatum_prod {ST SG SG' SB S : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (hd' : d'.Ok) (fr : Frs E a SB) (fr' : Frs E b SB)
    (hfr : ∀ (P : SB) x, fr P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1) (hfr' : ∀ (P : SB) x, fr' P x ∈ d'.at P.1 ↔ x ∈ stdAt E b P.1)
    (hS : ∀ P, P ∈ S ↔ P ∈ ST ∨ P ∈ SB) (c : ℕ) (hc : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (Φ : SB → HomE E a b → K) (β : SB → ℝ) (hΦ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Φ P) (β P)) :
    SmallDatum S d.N d'.N c (fun x => phiT K d d' x * ∏ P : SB, Φ P (inFr (fr P) (fr' P) x)) (∏ P : SB, β P) := by
  refine ⟨fun x hx P hP => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · rcases (hS P).1 hP with h | h
    · exact phiT_support d d' x (left_ne_zero_of_mul hx) P h
    · have h1 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) ⟨P, h⟩ (Finset.mem_univ _)
      exact (inFr_maps_iff _ _ (hfr ⟨P, h⟩) (hfr' ⟨P, h⟩) x).1 ((hΦ ⟨P, h⟩).1 _ h1)
  · obtain ⟨z, hz, rfl⟩ := hy
    have e : ((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z = (c : 𝓞 E) • z := rfl
    rw [e]
    show phiT K d d' _ * _ = phiT K d d' _ * _
    rw [phiT_add d d' hd' _ hc x z (fun P hP => hz P ((hS P).2 (Or.inl hP)))]
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk⟩ := hq P
    rw [hk, inFr_add_smul]
    refine (hΦ P).2.1 _ _ ?_
    refine (inFr_maps_iff _ _ (hfr P) (hfr' P) _).2 fun y hy => ?_
    exact Submodule.smul_mem _ (k : 𝓞 E) (hz P.1 ((hS P.1).2 (Or.inr P.2)) y hy)
  · show ‖σ (phiT K d d' x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ ≤ ∏ P : SB, β P :=
      Finset.prod_le_prod₀ (fun P _ => norm_nonneg _) fun P _ => (hΦ P).2.2 σ _
    have h0 : 0 ≤ ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ := Finset.prod_nonneg fun P _ => norm_nonneg _
    exact (mul_le_of_le_one_left h0 (norm_phiT_le d d' σ x)).trans h1

end EntryDatum

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUSuppSub

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R)

theorem fix_mul {A B : Matrix n n R} (hA : c • (A - 1) = A - 1) (hB : c • (B - 1) = B - 1) :
    c • (A * B - 1) = A * B - 1 := by
  have e : A * B - 1 = (A - 1) * B + (B - 1) := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hA, hB]

theorem fix_inv {A A' : Matrix n n R} (h : A' * A = 1) (hA : c • (A - 1) = A - 1) :
    c • (A' - 1) = A' - 1 := by
  have e : A' - 1 = -(A' * (A - 1)) := by rw [Matrix.mul_sub, h, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hA]

theorem fix_conj {A K K' : Matrix n n R} (h : K * K' = 1) (hA : c • (A - 1) = A - 1) :
    c • (K * A * K' - 1) = K * A * K' - 1 := by
  have e : K * A * K' - 1 = K * (A - 1) * K' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hA]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

abbrev mv (g : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))

theorem mv_mul (g h : HA (AF F) σ J) : mv σ J (g * h) = mv σ J g * mv σ J h := rfl

theorem mv_one : mv σ J 1 = 1 := rfl

theorem mv_inv_mul (g : HA (AF F) σ J) : mv σ J g⁻¹ * mv σ J g = 1 := by
  rw [← mv_mul, inv_mul_cancel, mv_one]

theorem mv_mul_inv (g : HA (AF F) σ J) : mv σ J g * mv σ J g⁻¹ = 1 := by
  rw [← mv_mul, mul_inv_cancel, mv_one]

theorem mem_SUSupp_iff {ε : AF F} {g : HA (AF F) σ J} : g ∈ SUSupp σ J ε ↔ g ∈ SUAdelic σ J ∧
    algebraMap (AF F) (AF F ⊗[F] E) ε • (mv σ J g - 1) = mv σ J g - 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext i j
    simpa using h2 i j
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j => ?_⟩
    have := congrFun (congrFun h2 i) j
    simpa using this

theorem closure_div_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, ∀ y ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}, x * y⁻¹ ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro F E _ _ _ _ _ σ _ M J _ S₁ S₂ ε _
  set c := algebraMap (AF F) (AF F ⊗[F] E) ε with hc
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hconj : ∀ k g : HA (AF F) σ J, g ∈ SUAdelic σ J → k * g * k⁻¹ ∈ SUAdelic σ J := by
    intro k g hg
    rw [StrongApprox.mem_SUAdelic] at hg ⊢
    change (mv σ J g).det = 1 at hg
    change (mv σ J (k * g * k⁻¹)).det = 1
    rw [mv_mul, mv_mul, Matrix.det_mul, Matrix.det_mul, hg, mul_one, ← Matrix.det_mul, mv_mul_inv,
      Matrix.det_one]
  have hdiv : ∀ x ∈ S, ∀ y ∈ S, x * y⁻¹ ∈ S := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩ _ ⟨γ', hγ', h', hh', rfl⟩
    refine ⟨γ * γ'⁻¹, (SURat σ J).mul_mem hγ ((SURat σ J).inv_mem hγ'), γ' * (h * h'⁻¹) * γ'⁻¹, ?_, by group⟩
    rw [mem_SUSupp_iff] at hh hh' ⊢
    refine ⟨hconj γ' _ ((SUAdelic σ J).mul_mem hh.1 ((SUAdelic σ J).inv_mem hh'.1)), ?_⟩
    rw [mv_mul, mv_mul, mv_mul]
    exact fix_conj _ (mv_mul_inv σ J γ') (fix_mul _ hh.2 (fix_inv _ (mv_inv_mul σ J h') hh'.2))
  have hne : S.Nonempty := ⟨1, 1, (SURat σ J).one_mem, 1,
    (mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [mv_one, sub_self, smul_zero]⟩, by simp⟩
  let P : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv S hne hdiv
  have hP : (P.topologicalClosure : Set (HA (AF F) σ J)) = closure S := by
    rw [Subgroup.topologicalClosure_coe]; rfl
  intro x hx y hy
  rw [← hP] at hx hy ⊢
  exact P.topologicalClosure.mul_mem hx (P.topologicalClosure.inv_mem hy)

end GlobalTheory.SUSuppSub

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTensorRetractOfCmDatumRankOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem smul_comm_of_finrank_one (D : Datum H) (h : Module.finrank (𝓞 E) D.La = 1)
    (l : D.La →ₗ[𝓞 E] 𝓞 E) (x y : D.La) : l x • y = l y • x := by
  have := D.fin
  have := D.proj
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul h hx y
  have hl : r * l y = s * l x := by rw [← smul_eq_mul, ← map_smul, e, map_smul, smul_eq_mul]
  have h0 : r • (l x • y - l y • x) = 0 := by
    rw [smul_sub, smul_comm r (l x) y, e, smul_smul, smul_smul, hl, mul_comm, sub_self]
  rw [smul_eq_zero] at h0
  exact sub_eq_zero.1 (h0.resolve_left hr)

theorem exists_dualBasis (D : Datum H) :
    ∃ (n : ℕ) (a : Fin n → D.La) (l : Fin n → (D.La →ₗ[𝓞 E] 𝓞 E)), ∀ x, ∑ k, l k x • a k = x := by
  have := D.fin
  have := D.proj
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) D.La
  refine ⟨n, fun k => f (fun j => if k = j then 1 else 0), fun k => LinearMap.proj k ∘ₗ g, fun x => ?_⟩
  have hx : f (g x) = x := LinearMap.congr_fun hfg x
  conv_rhs => rw [← hx, LinearMap.pi_apply_eq_sum_univ f (g x)]
  rfl

theorem exists_sum_comp_eq_id (DA DB : Datum H) (hA : DA.p + DA.q = 1) :
    ∃ (n : ℕ) (α : Fin n → (DA.La →ₗ[𝓞 E] DB.La)) (β : Fin n → (DB.La →ₗ[𝓞 E] DA.La)),
      ∑ i, α i ∘ₗ β i = LinearMap.id := by
  have := DA.fin
  have := DA.proj
  have hr : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hA]
  obtain ⟨n, a, l, decA⟩ := exists_dualBasis DA
  obtain ⟨m, b, mu, decB⟩ := exists_dualBasis DB
  have tr : ∑ k, l k (a k) = 1 := by
    have : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
    obtain ⟨x, hx⟩ := exists_ne (0 : DA.La)
    have e : (∑ k, l k (a k)) • x = (1 : 𝓞 E) • x := by
      rw [Finset.sum_smul, one_smul]
      conv_rhs => rw [← decA x]
      exact Finset.sum_congr rfl fun k _ => smul_comm_of_finrank_one DA hr (l k) (a k) x
    have h0 : ((∑ k, l k (a k)) - 1) • x = 0 := by rw [sub_smul, e, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx)
  refine ⟨n * m, fun i => (l (finProdFinEquiv.symm i).1).smulRight (b (finProdFinEquiv.symm i).2),
    fun i => (mu (finProdFinEquiv.symm i).2).smulRight (a (finProdFinEquiv.symm i).1), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin n × Fin m =>
    ((l p.1).smulRight (b p.2) ∘ₗ (mu p.2).smulRight (a p.1)) y), Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [← decB y]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul]
  rw [← Finset.sum_smul, ← Finset.mul_sum, tr, _root_.mul_one]

end GlobalTheory.CM
end

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {ω : R}
  {C : Ell H R ω}

theorem IsTen.isLinearHom_mapLeft {A B : PAT H (Sp R)} {DA DB : Datum H} {hA : DA.La → DA.La → OK H}
    {hB : DB.La → DB.La → OK H} (tA : IsTen C DA hA A) (tB : IsTen C DB hB B) (φ : DA.La →ₗ[𝓞 E] DB.La) :
    Serre.IsLinearHom A.t.act B.t.act (tA.ten.mapLeft tB.ten (φ.restrictScalars (OK H))) := by
  refine ⟨inferInstance, fun s => ?_⟩
  have := A.t.act.hom s
  have := B.t.act.hom s
  refine tA.ten.hom_ext fun m => ?_
  rw [← Category.assoc, ← tA.lin, Serre.IsTensor.tmul_mapLeft, ← Category.assoc, Serre.IsTensor.tmul_mapLeft,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, map_smul, tB.lin]

theorem IsTen.prod_mapLeft {B : PAT H (Sp R)} {DB : Datum H} {hB : DB.La → DB.La → OK H}
    (tB : IsTen C DB hB B) {I : Type} (s : Finset I) (φ : I → (DB.La →ₗ[𝓞 E] DB.La)) :
    ∏ i ∈ s, tB.ten.mapLeft tB.ten ((φ i).restrictScalars (OK H)) =
      tB.ten.mapLeft tB.ten ((∑ i ∈ s, φ i).restrictScalars (OK H)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, LinearMap.restrictScalars_zero, Serre.IsTensor.mapLeft_zero]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, LinearMap.restrictScalars_add, Serre.IsTensor.mapLeft_add]

theorem isTen_retract_of_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (A B : PAT H (Sp R)) (DA DB : Datum H)
    (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H), DA.p + DA.q = 1 → IsTen C DA hA A → IsTen C DB hB B →
    ∃ (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G)) (g : Fin n → (B.t.G ⟶ A.t.G)),
      (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) ∧ (∀ i, Serre.IsLinearHom B.t.act A.t.act (g i)) ∧
      ∏ i, (g i ≫ f i) = 𝟙 B.t.G := by
  intro E _ _ _ H R _ ω C A B DA DB hA hB h tA tB
  obtain ⟨n, α, β, hαβ⟩ := exists_sum_comp_eq_id DA DB h
  refine ⟨n, fun i => tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H)),
    fun i => tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)),
    fun i => tA.isLinearHom_mapLeft tB (α i), fun i => tB.isLinearHom_mapLeft tA (β i), ?_⟩
  have e : ∀ i, tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)) ≫ tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H))
      = tB.ten.mapLeft tB.ten ((α i ∘ₗ β i).restrictScalars (OK H)) := fun i =>
    (Serre.IsTensor.mapLeft_comp _ _ _ _ _).symm
  simp only [e]
  rw [tB.prod_mapLeft, hαβ]
  exact Serre.IsTensor.mapLeft_id _

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRapidDecayOneSimpleRootStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_rapidDecay_one_simpleRoot : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a → (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) → ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∀ Ω : Set (GA E a), IsCompact Ω → Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) → ∀ (t C₀ : ℝ) (N₀ : ℕ), 0 < t → (∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C₀ * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀) → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ i j : Fin a, (j : ℕ) = i + 1 → ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k)‖ ≤ C * (r j / r i) ^ m * (∑ i, (r i + (r i)⁻¹)) ^ N₀ := by
  first | exact @GlobalTheory.HCF.Decay.decay | exact GlobalTheory.HCF.Decay.decay | (intros; apply GlobalTheory.HCF.Decay.decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  first | (exact @GlobalTheory.HomFixUniv.eq_of_proport) | (exact GlobalTheory.HomFixUniv.eq_of_proport) | (intros; apply GlobalTheory.HomFixUniv.eq_of_proport  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFuncStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc : GlobalTheory.EtC.C1 := by
  first | (exact @GlobalTheory.EtC.gaugeSplitting_holds) | (exact GlobalTheory.EtC.gaugeSplitting_holds) | (intros; apply GlobalTheory.EtC.gaugeSplitting_holds  <;> assumption)
end

