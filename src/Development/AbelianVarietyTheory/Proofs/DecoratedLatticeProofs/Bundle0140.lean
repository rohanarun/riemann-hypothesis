module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueCompletionMatrixOfRationalTwistAut
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.MatGL
open GlobalTheory.SymBridge

def ordY (κ τ j c n : ℕ) (h : κ + j + j * τ + c = n) : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin n :=
  ((Equiv.sumCongr ((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv) (Equiv.refl (Fin c))).trans
    finSumFinEquiv).trans (finCongr h)

theorem ordY_isOrd (κ τ j c n : ℕ) (h : κ + j + j * τ + c = n) :
    IsOrd (yPos xPos (κ + j + j * τ)) (ordY κ τ j c n h) := by
  rintro (((i | i) | ⟨p, r⟩) | i)
  all_goals simp [ordY, yPos, xPos, finProdFinEquiv]
  all_goals ring

theorem isOrd_unique {A : Type} {n : ℕ} (pos : A → ℕ) (e e' : A ≃ Fin n) (he : IsOrd pos e) (he' : IsOrd pos e') : e = e' :=
  Equiv.ext fun a => Fin.ext ((he a).trans (he' a).symm)

variable {E k : Type} [Field E] [Field k]

theorem toLoc_eq (ι : E →+* k) {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : (Fin b → E) →ₗ[E] (Fin a → E)) :
    toLoc ι e e' x = ((LinearMap.toMatrix' x).submatrix e e').map ι := by
  ext i j
  simp [toLoc, LinearMap.toMatrix'_apply]

theorem toLoc_comp (ι : E →+* k) {A : Type} [Fintype A] {a : ℕ} (e : A ≃ Fin a) (x y : (Fin a → E) →ₗ[E] (Fin a → E)) :
    toLoc ι e e (x ∘ₗ y) = toLoc ι e e x * toLoc ι e e y := by
  rw [toLoc_eq, toLoc_eq, toLoc_eq, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ _ e, Matrix.map_mul]

theorem toLoc_id (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) :
    toLoc ι e e (LinearMap.id : (Fin a → E) →ₗ[E] (Fin a → E)) = 1 := by
  rw [toLoc_eq, LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv, Matrix.map_one _ (map_zero ι) (map_one ι)]

def toLocGL (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) (γ : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
    GL A k where
  val := toLoc ι e e γ.toLinearMap
  inv := toLoc ι e e γ.symm.toLinearMap
  val_inv := by rw [← toLoc_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, toLoc_id]
  inv_val := by rw [← toLoc_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, toLoc_id]

end GlobalTheory.TwBridge.MatGL

namespace GlobalTheory.TwBridge
open GlobalTheory.SymBridge MatGL

theorem existsUnique_isGL : ∀ (X : Fields) (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (j c : ℕ), c = cOf R j → ∀ γ : AutY X R j,
    ∃! g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin c) k, IsGL ι γ g := by
  intro X R k _ _ _ _ ι j c hc γ
  subst hc
  have hN : R.k + j + j * R.t = R.N j := by simp only [Ranks.N]; ring
  have hn : R.k + j + j * R.t + cOf R j = R.N j + cOf R j := by rw [hN]
  have ho : IsOrdY (ordY R.k R.t j (cOf R j) _ hn) := by
    have := ordY_isOrd R.k R.t j (cOf R j) _ hn
    rwa [hN] at this
  refine ⟨toLocGL ι (ordY R.k R.t j (cOf R j) _ hn) γ, ⟨_, ho, rfl⟩, ?_⟩
  rintro g ⟨e, he, hg⟩
  obtain rfl := isOrd_unique _ _ _ he ho
  exact Units.ext hg

end GlobalTheory.TwBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstStepCompletionRepresentativesEqOne
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.ZeroReps
open GlobalTheory.SymBridge

theorem toLoc_id {X : Fields} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : X.E →+* k) {A : Type} [DecidableEq A] {n : ℕ} (e : A ≃ Fin n) :
    toLoc ι e e (LinearMap.id : (Fin n → X.E) →ₗ[X.E] (Fin n → X.E)) = 1 := by
  ext i j
  simp only [toLoc, LinearMap.id_apply, Pi.single_apply, Matrix.one_apply, e.injective.eq_iff]
  split_ifs <;> simp

theorem exists_isOrdY_zero (R : Ranks) (c : ℕ) (hc : c = cOf R 0) :
    ∃ e : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c ≃ Fin (R.N 0 + cOf R 0), IsOrdY e := by
  classical
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hb : ∀ a : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c, yPos xPos (R.N 0) a < R.N 0 + cOf R 0 := by
    rintro (((i | i) | p) | i)
    · simp only [yPos, Sum.elim_inl, xPos]; omega
    · exact i.elim0
    · exact p.1.elim0
    · simp only [yPos, Sum.elim_inr]; omega
  let f : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c → Fin (R.N 0 + cOf R 0) := fun a => ⟨yPos xPos (R.N 0) a, hb a⟩
  have hf : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
    · rintro (((i | i) | p) | i) (((i' | i') | p') | i') hh <;>
        simp only [f, Fin.mk.injEq, yPos, Sum.elim_inl, Sum.elim_inr, xPos] at hh
      all_goals first
        | exact i.elim0 | exact i'.elim0 | exact p.1.elim0 | exact p'.1.elim0
        | (congr 1; first | (congr 2; exact Fin.ext hh) | exact Fin.ext (by omega))
        | omega
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      rw [hN]; omega
  exact ⟨Equiv.ofBijective f hf, fun a => rfl⟩

theorem reps_zero : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → _root_.GlobalTheory.TwBridge.AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), _root_.Formalism.L2.Col.ChIdx.Ok Ch sel mu cst L G s → IdxProd sel mu cst L → ∀ c (h : 0 + c = s), {g : GL (XIx (Fin R.k) (Fin R.t) (0) ⊕ Fin (c + 1)) k | ∃ b : L.β 0, IsGL ι (L.h 0 b P) g} = {1} := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA L G hL _ c h
  have hm : R.m = s + 2 := hA.steps
  have hcO : c + 1 = cOf R 0 := by unfold cOf; omega
  obtain ⟨b₀, -⟩ := hL.zero_uniq
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, e, -, hg⟩
    rw [hL.zero_h] at hg
    apply Units.ext
    rw [hg]
    exact toLoc_id ι e
  · rintro rfl
    obtain ⟨e, he⟩ := exists_isOrdY_zero R (c + 1) hcO
    refine ⟨b₀, e, he, ?_⟩
    rw [hL.zero_h]
    exact (toLoc_id ι e).symm

end GlobalTheory.TwBridge.ZeroReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentUnfoldingBesselFourierJacobiEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem zEll_mem_ratMx (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨Matrix.vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  funext i j
  change incA D (z i * (if j.1 + 1 = ρ then (1 : D.host.E) else 0)) = ratV z i * ell D ρ j
  simp only [ratV, ell]
  split_ifs <;> simp

theorem incAdj_yZero_mem {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Fin S.rank → D.host.E) :
    d.incAdj S (yZero S ρ z) ∈ ratMx D T.rank S.rank := by
  have hy : yZero S ρ z ∈ ratMx D S.rank ρ := by
    rw [yZero]; exact neg_mem (zEll_mem_ratMx S ρ z)
  rw [HypDec.incAdj_apply, HypDec.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    star (ψ x) = ψ (-x) := by
  change (starRingEnd ℂ) (ψ x) = _
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem integrand_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) (f : WO V₀ W → ℂ)
    (hf : IsThetaFunO ψ V₀ W f) (b : Mx D ρ V₀.rank) :
    star (psiBes ψ dV 1 z (dV.nB b)) * f (xZero dW ⬝ b) =
      heisO ψ V₀ W (dW.incX V₀ b) (heisO ψ V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (heisO ψ V₀ W (dW.inc0 V₀ 0) f)) 0 := by
  rw [HypDec.integrandT_eq, ← psi_yZero ψ dV dW z b, star_psi hψ, map_zero, add_zero]
  obtain ⟨γ, hγ⟩ := incAdj_yZero_mem dW V₀ z
  have hx : dW.incX V₀ b = xZero dW ⬝ b := rfl
  have hq := hf.quasi γ (xZero dW ⬝ b)
  rw [show ratW W V₀ γ = dW.incAdj V₀ (yZero V₀ ρ z) from hγ] at hq
  rw [hx, add_comm (xZero dW ⬝ b), hq, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hc : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  have hs : symplO V₀ W (xZero dW ⬝ b) (dW.incAdj V₀ (yZero V₀ ρ z)) =
      -symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b) := GlobalTheory.OrientedHeis.symplO_skew _ _
  rw [symplOH, symplOH]
  linear_combination (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b)) * hc -
    algebraMap D.host.F (AF D.host.F) (1 / 2) * hs

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

theorem fl_eq_flatBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ →
      fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flatBF s Ψ 0 := by
  intro D ψ ρ B J s Ψ hΨ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (_root_.GlobalTheory.MixValues.mixed_values D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flatBF flat flatAt
  congr 1
  funext u
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  unfold flFun flatFun evalAt
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact integrand_eq hψ B.d J.d _ _ (hf _) b

end GlobalTheory.Unf.StepFour
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockVecOfVac

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem coeff_sum_pderiv_eq_zero {ι : Type} [Fintype ι] (c : ι → ℂ) (Q : MvPolynomial ι ℂ) (n : ℕ)
    (hQ : ∀ m : ι →₀ ℕ, n < m.degree → Q.coeff m = 0) (m : ι →₀ ℕ) (hm : n < m.degree + 1) :
    (∑ i, c i • MvPolynomial.pderiv i Q).coeff m = 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_pderiv,
    hQ _ (by rw [map_add (f := _), Finsupp.degree_single]; omega), zero_mul, smul_zero]

theorem fock_of_vac : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsVacVec ψ θ M M' f → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ V W (cart M) (cart M') (ptOf ψ θ M M' f P) := by
  intro D V W S S' M M' θ ψ hψ hθ f hf P
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) (cart M τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M
  have hT : ∀ τ, IsCartanInv (gramAt D W τ) (cart M' τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M'
  set A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') with hAdef
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') := by
    intro g g' hg hg'
    refine { quasi := ?_, level := ?_, cont := hg.cont.add hg'.cont, smooth := ?_ }
    · intro γ w
      simp only [Pi.add_apply, hg.quasi, hg'.quasi, mul_add]
    · obtain ⟨U, hU, hUg⟩ := hg.level
      obtain ⟨U', hU', hUg'⟩ := hg'.level
      refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu hinf => ?_⟩
      have he : heisO ψ V W u (g + g') = heisO ψ V W u g + heisO ψ V W u g' := by
        funext w
        simp only [heisO, Pi.add_apply, mul_add]
      rw [he, hUg u hu.1 hinf, hUg' u hu.2 hinf]
    · intro k L hL hfin w
      simpa [Pi.add_apply] using (hg.smooth k L hL hfin w).add (hg'.smooth k L hL hfin w)
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) := by
    intro a g hg
    refine { quasi := ?_, level := ?_, cont := hg.cont.const_smul a, smooth := ?_ }
    · intro γ w
      simp only [Pi.smul_apply, smul_eq_mul, hg.quasi]
      ring
    · obtain ⟨U, hU, hUg⟩ := hg.level
      refine ⟨U, hU, fun u hu hinf => ?_⟩
      have he : heisO ψ V W u (a • g) = a • heisO ψ V W u g := by
        funext w
        simp only [heisO, Pi.smul_apply, smul_eq_mul]
        ring
      rw [he, hUg u hu hinf]
    · intro k L hL hfin w
      simpa [Pi.smul_apply] using (hg.smooth k L hL hfin w).const_smul a
  have hA : ∀ k g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (A k g) := fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ V W g → A i (A j g) = A j (A i g) :=
    fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ V W g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hpt : ∀ Q, ptOf ψ θ M M' f Q = pureTensorL A f Q := fun _ => rfl
  have hm : ∀ Q, IsThetaFunO ψ V W (pureTensorL A f Q) := pure_mem hadd hsm hA hf.theta

  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ c : FVar D W.rank V.rank → ℂ, ∀ Q,
      annih (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) z (pureTensorL A f Q) =
        pureTensorL A f (∑ i, c i • MvPolynomial.pderiv i Q) := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir V W τ z k.1 (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir V W τ (cplxO (cart M τ) (cart M' τ) z) k.1
          (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ))), fun Q => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.theta (hf.vac τ z) Q
  refine ⟨by rw [hpt]; exact hm P, P.totalDegree + 1, fun l hl => ?_⟩

  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Q : MvPolynomial (FVar D W.rank V.rank) ℂ,
      l.foldr (fun p g => annih (heisO ψ V W) θ p.1 (cplxO (cart M p.1) (cart M' p.1)) p.2 g) (pureTensorL A f P) =
        pureTensorL A f Q ∧ ∀ m : FVar D W.rank V.rank →₀ ℕ, P.totalDegree < m.degree + l.length → Q.coeff m = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨P, rfl, fun m hm' => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h' : P.totalDegree < m.degree := by simpa using hm'
      exact h'
    | cons p l ih =>
      obtain ⟨Q, hQ, hQc⟩ := ih
      obtain ⟨c, hc'⟩ := hder p.1 p.2
      refine ⟨∑ i, c i • MvPolynomial.pderiv i Q, ?_, fun m hm' => ?_⟩
      · rw [List.foldr_cons, hQ, hc']
      · refine coeff_sum_pderiv_eq_zero c Q (P.totalDegree - l.length) (fun m' hm'' => hQc m' (by omega)) m ?_
        simp only [List.length_cons] at hm'
        omega
  obtain ⟨Q, hQ, hQc⟩ := key l
  have hQ0 : Q = 0 := MvPolynomial.ext _ _ fun m => by
    simpa using hQc m (by rw [hl]; omega)
  rw [hpt, hQ, hQ0, map_zero]

end GlobalTheory.FockVecOfVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormMapRBijective
section
noncomputable section

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (pr : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)
  (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}

def clMapR (c : ((stepY ST y β Λ Θ pref).reRep pr).Cl) : (base ST lam Λ₀).Cl :=
  (base ST lam Λ₀).cls (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco

theorem clMapR_cl (hΛ : ∀ b, Λ b = Λ₀) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    clMapR (Λ₀ := Λ₀) pref pr lam (((stepY ST y β Λ Θ pref).reRep pr).cl b p) = (base ST lam Λ₀).cls p.1.1.deco := by
  have e := congrArg (fun q : (stepY ST y β Λ Θ pref).D b => q.1.1.deco) (((stepY ST y β Λ Θ pref).reRep pr).mv_smul b p)
  rw [← e]
  exact ((base ST lam Λ₀).cls_smul (down (y := y) pref hΛ b (((stepY ST y β Λ Θ pref).reRep pr).mv b p)) _).symm

theorem clMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    Function.Bijective (clMapR (Λ₀ := Λ₀) pref pr lam) := by
  refine ⟨?_, fun c₀ => ?_⟩
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    obtain rfl : b = b' := Subsingleton.elim (α := β) _ _
    obtain ⟨g₀, hg⟩ := ((base ST lam Λ₀).cls_eq_iff _ _).1 h
    obtain ⟨g, -, h2⟩ := exists_lift pref hy hΛ hΘ b _ _ g₀ hg
    congr 1
    rw [← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q, ← ((stepY ST y β Λ Θ pref).reRep pr).rp_spec b q']
    exact Quotient.sound ⟨g, h2⟩
  · induction c₀ using Quotient.inductionOn' with
    | h d =>
      obtain ⟨p, rfl⟩ := exists_pt (Q := Q) hy d
      exact ⟨((stepY ST y β Λ Θ pref).reRep pr).cl default p, clMapR_cl pref pr lam hΛ default p⟩

def clEquivR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    ((stepY ST y β Λ Θ pref).reRep pr).Cl ≃ (base ST lam Λ₀).Cl :=
  Equiv.ofBijective _ (clMapR_bijective pref pr lam hy hΛ hΘ)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pr).rep ((clEquivR pref pr lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := (clEquivR pref pr lam hy hΛ hΘ).apply_symm_apply c

def formMapR (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok) :
    (base ST lam Λ₀).EqFun →ₗ[X.K] ((stepY ST y β Λ Θ pref).reRep pr).FormsK X.emb lam h where
  toFun φ := ⟨fun c => φ.1 (((stepY ST y β Λ Θ pref).reRep pr).rep c).1.1.deco, fun c g =>
    (form_smul pref lam hΛ hΘ φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formMapR_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : (((stepY ST y β Λ Θ pref).reRep pr).fam X.emb lam).Ok)
    (h₀ : (base ST lam Λ₀).Ok) :
    Function.Bijective (formMapR pref pr lam hΛ hΘ h) := by
  refine ⟨fun φ ψ e => ?_, fun f => ?_⟩
  · apply ((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).injective
    apply Subtype.ext
    funext c
    exact congrFun (congrArg Subtype.val e) ((clEquivR pref pr lam hy hΛ hΘ).symm c)
  · let f₀ : ((base ST lam Λ₀).toCSDOf h₀ (secR pref pr lam hy hΛ hΘ)).Forms :=
      ⟨fun c => f.1 ((clEquivR pref pr lam hy hΛ hΘ).symm c), fun c g₀ => by
        obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ _ _ _ g₀.1 g₀.2
        have h3 := f.2 ((clEquivR pref pr lam hy hΛ hΘ).symm c) ⟨g, h2⟩
        have h4 := rho_eq pref lam hΛ hΘ _ g
        rw [h1] at h4
        exact (LinearMap.congr_fun h4 _).symm.trans h3⟩
    refine ⟨((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).symm f₀, Subtype.ext (funext fun c => ?_)⟩
    obtain ⟨c₀, rfl⟩ := (clEquivR pref pr lam hy hΛ hΘ).symm.surjective c
    exact congrFun (congrArg Subtype.val
      (((base ST lam Λ₀).resOf h₀ (secR pref pr lam hy hΛ hΘ)).apply_symm_apply f₀)) c₀

end Forget

theorem exists_colZeroR {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
    {G : ChGlob X R.m} {m2 : ℕ} (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
    (pr : ∀ b, (stepAt sel mu cst L Tp u 0).D b → Prop) (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2)
    (h : (((stepAt sel mu cst L Tp u 0).reRep pr).fam X.emb (lamT (W.hc u) 0)).Ok) :
    ∃ κ : MfV W Ch u ≃ₗ[X.K] ((stepAt sel mu cst L Tp u 0).reRep pr).FormsK X.emb (lamT (W.hc u) 0) h,
      ∀ φ c, (κ φ).1 c = φ.1 (((stepAt sel mu cst L Tp u 0).reRep pr).rep c).1.1.deco :=
  letI := idxUnique hL
  ⟨LinearEquiv.ofBijective _ (formMapR_bijective (Tp.pref u 0) pr (lamT (W.hc u) 0) (ysAt_zero sel mu cst)
    (levGAt_zero Tp hL) (levQAt_zero Tp hL) h (colOk W Ch hX u 0)), fun _ _ => rfl⟩

end GlobalTheory.Core.ColZero

namespace GlobalTheory.Core.ColZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_colEquiv {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (u : B.Word) (a : I.ι) :
    ∃ κ : ColsK I u ≃ₗ[B.fields.K] ((I.fm l u a).lat 0).V, ∀ φ, IsCol I u a l (κ φ) φ :=
  exists_colZeroR (Pr := B.primes X) B.wts (I.Tp a) u (I.pref u a 0) hX (h.idx_ok a) ((l.fmL u a).fam 0)

end GlobalTheory.Core.ColZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HostFieldsPrimesTies
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem host_fields_primes_ties : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.rec7 l Z).host.ccK = ⊤ ∧ GL3Theta.InducedCMType (I.rec7 l Z) ∧ GL3Theta.HostFieldConditions (I.rec7 l Z) ∧ B.fields.AbelianUnramifiedExtensionConditions ∧ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).Ok ∧ (∀ x : B.fields.K, B.embLL (star x) = starRingEnd ℂ (B.embLL x)) ∧ (B.primes X).Ok ∧ (B.primes X).PiGCong ∧ (B.primes X).cond = B.host.QS * B.host.q * B.host.d ∧ (∀ i, (B.primes X).g i = B.host.g i) ∧ B.wts.Ok := by
  intro B X I _ _ l Z
  exact ⟨B.toPre.ccK_top, GlobalTheory.InducedType.restrict_K _, Formalism.MainNotions.GL3Theta.cm_field_facts_hold _, (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1,
    seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G, B.starLL_cx, (GlobalTheory.BasePrimes.primes_ok B X).1, (GlobalTheory.BasePrimes.primes_ok B X).2,
    rfl, fun _ => rfl, B.wts_isOk⟩

end GlobalTheory.Core.Ht2
end

