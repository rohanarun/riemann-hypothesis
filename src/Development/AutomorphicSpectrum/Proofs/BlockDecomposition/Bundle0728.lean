module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0725
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0713
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0721
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0724
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombination
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MixZ

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a)
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem multicone_of_isUnder {U : (MP ℤ m n).Opens} {c : ∀ k, Bk n k} {y : CxPts (mpStr ℤ m n) σ₀}
    {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (U ⊓ mchart c)) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun k =>
  ⟨c k, ((hz k (c k)).1).1 (CxPts.ptsIn_mono (inf_le_right.trans (mchart_le c k)) hy)⟩

theorem isHermRep_congr {M : HermLB (mpStr ℤ m n)} {A B : HermLine (Bk n)} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z)
    (hM : IsHermRep M A) : IsHermRep M B := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨u, h₁, ?_, ?_⟩
  · rw [← ha]
    exact h₂
  · intro i c y z hz hy
    rw [← hh z (multicone_of_isUnder hz hy), ← ha]
    exact h₃ i c y z hz hy

theorem isHermRep_zp {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hM : IsHermRep M A) (e : ℤ) :
    ∃ B : HermLine (Bk n), IsHermRep (zp M e) B ∧ B.a = e • A.a ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = A.h z ^ e := by
  refine ⟨(powLine A e.toNat).tensor (powLine A (-e).toNat).inv,
    isHermRep_tens _ _ _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)
      (isHermRep_dual _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)), ?_, ?_⟩
  · funext k
    have e₁ : ((e.toNat : ℤ) - ((-e).toNat : ℤ)) = e := by omega
    simp only [HermLine.tensor, HermLine.inv, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, powLine_a, smul_eq_mul]
    linear_combination (A.a k) * e₁
  · intro z hz
    have hp := (A.pos z hz).ne'
    simp only [HermLine.tensor, HermLine.inv, PowRep.h_powLine]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp]
    congr 1
    omega

theorem isHermRep_foldr {κ : Type} (M : κ → HermLB (mpStr ℤ m n)) (A : κ → HermLine (Bk n))
    (hM : ∀ o, IsHermRep (M o) (A o)) (a : κ → ℤ) (l : List κ) :
    ∃ B : HermLine (Bk n), IsHermRep (l.foldr (fun i N => (zp (M i) (a i)).tens N) (HermLB.triv (mpStr ℤ m n))) B ∧
      B.a = (l.map fun o => a o • (A o).a).sum ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = (l.map fun o => (A o).h z ^ a o).prod := by
  induction l with
  | nil =>
    exact ⟨_, isHermRep_triv m n, by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine], fun z _ => by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]⟩
  | cons o l ih =>
    obtain ⟨B, hB, ha, hh⟩ := ih
    obtain ⟨C, hC, ca, ch⟩ := isHermRep_zp (hM o) (a o)
    refine ⟨C.tensor B, isHermRep_tens _ _ _ _ _ _ hC hB, ?_, fun z hz => ?_⟩
    · simp only [HermLine.tensor, List.map_cons, List.sum_cons, ca, ha]
    · simp only [HermLine.tensor, List.map_cons, List.prod_cons, ch z hz, hh z hz]

theorem readComb : ReadComb := by
  intro m n κ _ M A hM a
  obtain ⟨B, hB, ha, hh⟩ := isHermRep_foldr M A hM a (Finset.univ : Finset κ).toList
  refine isHermRep_congr ?_ (fun z hz => ?_) hB
  · rw [ha, Finset.sum_map_toList]
    rfl
  · rw [hh z hz, Finset.prod_map_toList]
    exact (if_pos hz).symm

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.ZUnf

section Rows

variable {K : Type} [Field K] {n ρ p : ℕ}

def zinc (hn : ρ + p = n) : (Fin ρ → K) →ₗ[K] (Fin n → K) where
  toFun u i := Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm i)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp

def wM (hn : ρ + p = n) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1)

def nM (hn : ρ + p = n) (ζ : Matrix (Fin ρ) (Fin ρ) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 1 (bl hn ζ 0 0 0) 0 1

def sM (hn : ρ + p = n) (σ : K →+* K) (η : Matrix (Fin ρ) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 η 0 1) 0 0 (bl hn 1 0 (-cT σ η) 1)

def eM (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)

def rowC (hn : ρ + p = n) (η : Matrix (Fin ρ) (Fin p) K) (a c : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-1) (-(η * a)) 0 c

def rowD (hn : ρ + p = n) (σ : K →+* K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K)
    (b d : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-ζ) (-(η * b)) (-cT σ η) d

end Rows

variable {D : D7} {n ρ p : ℕ}

def zKer (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin ρ → D.host.E) :=
  (cellKer x).comap (zinc hn)

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRightInv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open _root_.Topology GlobalTheory.SplitWeil

theorem fibInt_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (f : cIndSpace (HPG k i t) (hRep τ σ)) (x g : GL (Fin (i + t)) k), fibInt μ (prodPG τ σ (levi k (i + t) x) f) g = fibInt μ f (g * x) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ f x g
  have h : fibV (prodPG τ σ (levi k (i + t) x) f) g = fibV f (g * x) := funext fun v =>
    congrArg f.1.1.1 (show uM k (i + t) (midV k i t v) * levi k (i + t) g * levi k (i + t) x =
      uM k (i + t) (midV k i t v) * levi k (i + t) (g * x) by rw [map_mul, mul_assoc])
  exact congrArg (fun φ => clT τ W (smInt μ φ)) h

theorem fibInt_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (g : GL (Fin (i + t)) k), (∀ f₁ f₂ : cIndSpace (HPG k i t) (hRep τ σ), fibInt μ (f₁ + f₂) g = fibInt μ f₁ g + fibInt μ f₂ g) ∧ ∀ (a : ℂ) (f : cIndSpace (HPG k i t) (hRep τ σ)), fibInt μ (a • f) g = a • fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ g
  have hr := fun f => _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.fibV_main k i t τ σ hτ hσ f g
  have hp := SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ
  refine ⟨fun f₁ f₂ => ?_, fun a f => ?_⟩
  · have h : smInt μ (fibV (f₁ + f₂) g) = smInt μ (fibV f₁ g) + smInt μ (fibV f₂ g) :=
      hp.1 (fibV f₁ g) (fibV f₂ g) (hr f₁).1 (hr f₁).2 (hr f₂).1 (hr f₂).2
    exact (congrArg (clT τ W) h).trans (map_add _ _ _)
  · have e : fibV (a • f) g = (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) ∘ fibV f g :=
      funext fun v => map_smul (evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) g)) a f
    have h1 := hp.2.1 (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) (fibV f g) (hr f).1 (hr f).2
    have h : smInt μ (fibV (a • f) g) = a • smInt μ (fibV f g) := (congrArg (smInt μ) e).trans h1
    exact (congrArg (clT τ W) h).trans (map_smul _ _ _)

theorem exists_nhds_prod {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X → Y → Z) (hF : Continuous fun p : X × Y => F p.1 p.2) (x : X) (y : Y) {U : Set Z} (hU : U ∈ 𝓝 (F x y)) :
    ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ a ∈ A, ∀ b ∈ B, F a b ∈ U := by
  have h : (fun p : X × Y => F p.1 p.2) ⁻¹' U ∈ 𝓝 (x, y) := hF.continuousAt.preimage_mem_nhds hU
  rw [nhds_prod_eq, Filter.mem_prod_iff] at h
  obtain ⟨A, hA, B, hB, hsub⟩ := h
  exact ⟨A, hA, B, hB, fun a ha b hb => hsub (Set.mk_mem_prod ha hb)⟩

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_latt_nhds {n : ℕ} {U : Set (Mir k n)} (hU : U ∈ 𝓝 (1 : Mir k n)) :
    ∃ c : kˣ, ∃ A ∈ 𝓝 (1 : GL (Fin n) k), ∀ y ∈ latt n c, ∀ b ∈ A, uM k n y * levi k n b ∈ U := by
  have hc := _root_.GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k n
  have hcont : Continuous fun p : (Fin n → k) × GL (Fin n) k => uM k n p.1 * levi k n p.2 :=
    (hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd)
  have h00 : uM k n 0 * levi k n 1 = 1 := by rw [uM_zero, map_one, one_mul]
  obtain ⟨A, hA, B, hB, h⟩ := exists_nhds_prod (fun y b => uM k n y * levi k n b) hcont 0 1
    (by rw [h00]; exact hU)
  obtain ⟨c, hcA⟩ := exists_latt_subset hA
  exact ⟨c, B, hB, fun y hy b hb => h y (hcA hy) b hb⟩

theorem exists_level {n : ℕ} {Z : Type} (Zs : Set Z) (hZ : Zs.Finite) (U : Z → Set (Mir k n))
    (hU : ∀ z, U z ∈ 𝓝 (1 : Mir k n)) {A' : Set (GL (Fin n) k)} (hA' : A' ∈ 𝓝 (1 : GL (Fin n) k)) :
    ∃ (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (hK : K₁ ≤ KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) ∧
      (K₁ : Set (GL (Fin n) k)) ⊆ A' ∧ K₁.relIndex (KO k (Fin n)) ≠ 0 ∧
      (∀ κ ∈ KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) ∧ ∀ z ∈ Zs, ∀ p ∈ Bgrp n c K₁ hK, p ∈ U z := by
  have hI : (⋂ z ∈ Zs, U z) ∈ 𝓝 (1 : Mir k n) := (Filter.biInter_mem hZ).2 fun z _ => hU z
  obtain ⟨c, A, hA, hcA⟩ := exists_latt_nhds hI
  obtain ⟨K₁, hK, hopen, hsub, hidx, hnorm⟩ := GlobalTheory.T.exists_normal_open_subgroup_compact k n _ (Filter.inter_mem hA hA')
  refine ⟨c, K₁, hK, hopen, fun x hx => (hsub hx).2, hidx, hnorm, ?_⟩
  rintro z hz _ ⟨y, hy, b, hb, rfl⟩
  exact Set.mem_iInter₂.1 (hcA y hy b (hsub hb).1) z hz

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] (GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W) where
  toFun f := fun g => fibInt μ f g
  map_add' f₁ f₂ := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).1 f₁ f₂
  map_smul' a f := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).2 a f

theorem clT_surjective (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Function.Surjective (clT τ W) :=
  LinearMap.rTensor_surjective W (Submodule.mkQ_surjective _)

theorem exists_bump_fib (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ b : cIndSpace (HPG k i t) (hRep τ σ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, fibInt μ b ((q : GL (Fin (i + t)) k) * b') =
        (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • qRep τ σ q (clT τ W z)) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  have hBo := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp k (i + t) c K₁ hK hopen
  obtain ⟨b, hb1, hb2⟩ := _root_.GlobalTheory.CompanionTheory.HBBump.exists_bump (HPG k i t) (hRep τ σ) (Bgrp (i + t) c K₁ hK) hBo.1 hBo.2 z hz
  have hone : fibInt μ b 1 = (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • clT τ W z := by
    have h1 := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.fibV_one_bump k i t τ σ c K₁ hK z b hb1 hb2
    have h2 := (SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).2.2.2 _ z (isCompact_latt t c)
      (isOpen_latt t c) (isClosed_latt t c)
    exact (congrArg (fun φ => clT τ W (smInt μ φ)) h1).trans ((congrArg (clT τ W) h2).trans (map_smul _ _ _))
  refine ⟨b, fun q b' hb' => ?_, _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main k i t τ σ μ c K₁ hK b hb2⟩
  have e1 : fibInt μ b b' = fibInt μ b 1 := by
    have h := _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibInvK.fibV_mul_right_eq k i t τ σ c K₁ hK z b hb1 hb2 b' hb' 1
    have h' : fibV b b' = fibV b 1 := (congrArg (fibV b) (one_mul b').symm).trans h
    exact congrArg (fun φ => clT τ W (smInt μ φ)) h'
  exact (_root_.GlobalTheory.CompanionTheory.BZPsiPG.FibQ.main k i t τ σ hτ hσ μ b q b').trans
    ((congrArg (qRep τ σ q) (e1.trans hone)).trans (map_smul _ _ _))

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open _root_.Topology GlobalTheory.SplitWeil

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem smooth_right_inv {Γ J : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup J] [Module ℂ J]
    (H : Subgroup Γ) (π : Representation ℂ H J) (G : smoothPart (ind H π)) :
    {s : Γ | ∀ x, G.1.1 (x * s) = G.1.1 x} ∈ 𝓝 (1 : Γ) := by
  have h1 : {s : Γ | ind H π s G.1 = G.1} ∈ 𝓝 (1 : Γ) := IsOpen.mem_nhds G.2 (by simp)
  exact Filter.mem_of_superset h1 fun s hs x => congrFun (congrArg Subtype.val hs) x

theorem exists_fib_mem (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W) (a : Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (ha : clT τ W z = a)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ φ ∈ LinearMap.range (fibLin τ σ hτ hσ μ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, φ ((q : GL (Fin (i + t)) k) * b') = qRep τ σ q a) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → φ g = 0 := by
  subst ha
  have hcc0 : (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) ≠ 0 := by
    have h1 : 0 < μ (latt t c : Set (Fin t → k)) := (isOpen_latt t c).measure_pos μ ⟨0, zero_mem _⟩
    have h2 : μ (latt t c : Set (Fin t → k)) ≠ ⊤ := (isCompact_latt t c).measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  refine Exists.elim (exists_bump_fib τ σ hτ hσ μ c K₁ hK hopen z hz) fun b hb => ?_
  refine ⟨(((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • (fibLin τ σ hτ hσ μ b),
    Submodule.smul_mem _ _ ⟨b, rfl⟩, fun q b' hb' => ?_, fun g hg => ?_⟩
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.1 q b' hb')).trans
      (inv_smul_smul₀ hcc0 _)
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.2 g hg)).trans (smul_zero _)

theorem mem_range_fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (Gf : GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (hlaw : ∀ (q : Qp k i t) (g : GL (Fin (i + t)) k), Gf ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (Gf g))
    (hinv : {s : GL (Fin (i + t)) k | ∀ x, Gf (x * s) = Gf x} ∈ 𝓝 (1 : GL (Fin (i + t)) k)) :
    Gf ∈ LinearMap.range (fibLin τ σ hτ hσ μ) := by
  have hfin : (Gf '' (KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite :=
    _root_.GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one _ GlobalTheory.SplitFlip.isCompact_KO Gf hinv
  obtain ⟨pre, hpre⟩ : ∃ pre : Jacquet τ (MirUin k i) ⊗[ℂ] W → V ⊗[ℂ] W, ∀ a, clT τ W (pre a) = a :=
    ⟨Function.surjInv (clT_surjective τ W), Function.surjInv_eq _⟩
  choose Ust hUst hUfix using _root_.GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix k i t τ σ hτ hσ
  obtain ⟨c, K₁, hK, hopen, hsub, hidx, hnorm, hlev⟩ := exists_level _ (hfin.image pre) Ust hUst hinv
  have hfix : ∀ κ ∈ KO k (Fin (i + t)), ∀ h : HPG k i t,
      (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h (pre (Gf κ)) = pre (Gf κ) :=
    fun κ hκ h hh => hUfix _ h (hlev _ ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩ _ hh)
  refine _root_.GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps (Qp k i t) (KO k (Fin (i + t))) K₁ (qRep τ σ) (LinearMap.range (fibLin τ σ hτ hσ μ)) Gf hK hidx hnorm
    (fun g => ?_) ?_ ?_ hlaw (fun g b hb => hsub hb g) ?_
  · obtain ⟨q, κ, hκ, e⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO k i t g
    exact ⟨q, κ, hκ, e⟩
  · rintro _ ⟨f, rfl⟩ x
    exact ⟨prodPG τ σ (levi k (i + t) x) f, funext fun g => fibInt_translate k i t τ σ μ f x g⟩
  · rintro _ ⟨f, rfl⟩ q g
    exact _root_.GlobalTheory.CompanionTheory.BZPsiPG.FibQ.main k i t τ σ hτ hσ μ f q g
  · intro κ hκ
    exact exists_fib_mem τ σ hτ hσ μ c K₁ hK hopen (pre (Gf κ)) (Gf κ) (hpre _) (hfix κ hκ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG

open _root_.Topology GlobalTheory.SplitWeil FibOnto

theorem exists_fibInt_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ G : smoothPart (ind (Qp k i t) (qRep τ σ)), ∃ f : cIndSpace (HPG k i t) (hRep τ σ), ∀ g, fibInt μ f g = G.1.1 g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ G
  have hM := mem_range_fibLin τ σ hτ hσ μ G.1.1 G.1.2 (smooth_right_inv _ _ G)
  exact ⟨Classical.choose hM, fun g => congrFun (Classical.choose_spec hM) g⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwap
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem term_after : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ hTw χ' hχ' θ hθ Ω hΩ χ s f hf g γ hγ T hT v
  obtain ⟨z', hz'⟩ := hT v.1 v.2
  have hz : M.emb γ * (M.nzx 0 v.2 * M.sh v.1) = M.nzx z' (T v).2 * M.sh (T v).1 * M.emb γ := hz'
  have hterm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      Wz M m ψ b₀ f (M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))) =
        chz ψ b₀ z' * (chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) := by
    intro η
    have e1 : M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)) =
        M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
      calc M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))
          = M.sh (rt η) * ((M.emb γ * (M.nzx 0 v.2 * M.sh v.1)) * g) := by simp only [mul_assoc]
        _ = M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
            rw [hz]; simp only [mul_assoc]
    have e2 : M.sh (rt η) * (M.sh (T v).1 * M.emb γ * g) = M.sh (rt η + (T v).1) * M.emb γ * g := by
      rw [← sh_add M (rt η) (T v).1]; simp only [mul_assoc]
    rw [e1, _root_.GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx M m ψ hψ b₀ χ s f hf (rt η) z' (T v).2 _, e2, mul_assoc]
  obtain ⟨-, hnorm, -, -⟩ := GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀
  have hchv : ∀ x y : Mx D ρ p, ‖chv ψ b₀ x y‖ = 1 := fun x y => hψ.2.1 _
  have hth : th ψ b₀ (Ω 1) 0 v.2 v.1 = chz ψ b₀ z' * dsum ψ b₀ (Ω γ) (T v).2 (T v).1 := by
    rw [hTw D n ρ p hn M m ψ hψ b₀ hb₀ χ' hχ' θ hθ Ω hΩ γ hγ 0 v.2 v.1 z' (T v).2 (T v).1 hz]
    rfl
  have hcc : chz ψ b₀ z' * conj (chz ψ b₀ z') = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  refine ⟨fun η => ?_, ?_⟩
  · rw [hterm η, norm_mul, norm_mul, hnorm, hchv, one_mul, one_mul]
  · simp_rw [hterm]
    rw [tsum_mul_left, hth, map_mul, Ap]
    have hd : (∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
        chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) =
        dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 := rfl
    rw [hd]
    calc _ = (chz ψ b₀ z' * conj (chz ψ b₀ z')) *
          (dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 *
            conj (dsum ψ b₀ (Ω γ) (T v).2 (T v).1)) := by ring
      _ = _ := by rw [hcc, one_mul]

end GlobalTheory.CompanionTheory.FJE
end
end

