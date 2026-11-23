module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

def spAct {R : Type} [CommRing R] [Algebra F R] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    (κ → R) × (κ → R) :=
  (fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inl k),
    fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inr k))

def weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 0 1 (-1) 0

def leviM (A : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks A 0 0 A⁻¹ᵀ

def unipM (S : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 1 0 S 1

def IsSymp (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := G.transpose * weylM * G = weylM

def gens : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {G | ∃ A : Matrix κ κ F, IsUnit A.det ∧ G = leviM A} ∪ {G | ∃ S : Matrix κ κ F, S.transpose = S ∧ G = unipM S} ∪ {weylM}

variable [NumberField F]

def indO (v : Pl (F := F)) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def HasOp (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)

end GlobalTheory.SympChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitUnitLift

open GlobalTheory.SplitGLLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : Pl (F := F)} {n : ℕ}

theorem unitary_eps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g))ᵀ * incM F J *
      (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g)).map (cA σ) = incM F J := by
  set p := pairHom (J.map τ) hJ g - 1 with hp
  have hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p := rfl
  rw [hN, map_one_add_cA]
  have tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)),
      (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f := fun f A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have e : J.map τ * (J.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have gi : ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 :=
    Units.inv_mul g
  apply mat_ext h τ
  · intro w
    rw [tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]
    simp
  · intro u hu
    rw [tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]
    simp
  · rw [tr, map_one_add_piW, map_one_add_piW, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW τ) ∘ ⇑(inclR (F := F) (AF F))) = J.map τ :=
      Matrix.ext fun i j => piW_inclR τ (J i j)
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ *
      ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ) = J.map τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one,
      ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]
  · rw [tr, map_one_add_piW_comp, map_one_add_piW_comp, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW (τ.comp σ)) ∘ ⇑(inclR (F := F) (AF F))) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
      rw [piW_inclR, AlgHom.comp_apply, herm, map_mul, AlgHom.commutes]
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)ᵀ *
      (algebraMap F (Fv F v) ε • (J.map τ)ᵀ) * (g : Matrix (Fin n) (Fin n) (Fv F v)) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi,
      Matrix.mul_one]

def liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (oneAdd (liftMat h τ)).comp (pairHom (J.map τ) hJ)

def liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* UA σ J where
  toFun g := ⟨⟨liftN h τ J hJ g, liftN h τ J hJ g⁻¹, by rw [← map_mul, mul_inv_cancel, map_one],
    by rw [← map_mul, inv_mul_cancel, map_one]⟩, unitary_eps h τ J ε herm hJ g⟩
  map_one' := Subtype.ext (Units.ext (map_one (liftN h τ J hJ)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (liftN h τ J hJ) g g'))

theorem mat_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    mat (liftU h τ J ε herm hJ g) = 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1) := rfl

theorem liftU_mem_UAt (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (X : Spc F E n) (ε : F)
    (herm : ∀ i j, σ (X.J j i) = algebraMap F E ε * X.J i j) (hJ : IsUnit (X.J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    liftU h τ X.J ε herm hJ g ∈ UAt σ X (evFin F v) := by
  show At (evFin F v) (mat _ - 1)
  rw [mat_liftU, add_sub_cancel_left]
  exact at_liftMat h τ _

theorem liftU_piW (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW τ) = g.val := by
  rw [mat_liftU, map_one_add_piW]
  exact add_sub_cancel _ _

theorem liftU_piW_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW (τ.comp σ)) = (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * J.map τ := by
  rw [mat_liftU, map_one_add_piW_comp]
  exact add_sub_cancel _ _

theorem isUnit_det_of_cartan (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v) (e : E →+* ℂ) (c : ℂ) (hc : c ≠ 0)
    (θ : Matrix (Fin n) (Fin n) ℂ) (hθ : IsCartan (c • J.map e) θ) : IsUnit (J.map τ).det := by
  have h1 : (c • J.map e).det ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hx : star y ≠ 0 := fun h => hy (by simpa using congrArg star h)
    have := hθ.2.2 (star y) hx
    rw [star_star, hMy, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have h2 : J.det ≠ 0 := by
    intro h0
    apply h1
    have hd : (J.map e).det = e J.det := (RingHom.map_det e J).symm
    rw [Matrix.det_smul, hd, h0, map_zero, mul_zero]
  have hd : (J.map τ).det = τ J.det := (AlgHom.map_det τ J).symm
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 h2

end GlobalTheory.SplitUnitLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRouteInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_first_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (hd : d ∈ Θ.support) :
    IsThetaFunO W.ψ (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) (G.pT (.chi (i : ℕ) ((j : ℕ) + 1))) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, -⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _

theorem kerBig_rat_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g
  have hc := W.om_is (.chi (i : ℕ) ((j : ℕ) + 1)) ⟨i.2, j.2⟩
  funext u
  unfold kerBig
  refine Finsupp.sum_congr fun d hd => ?_
  have h1 := theta_first_of_matched hΘ hd
  congr 2
  show thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) (γ * g) d.1.2 =
    thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) g d.1.2
  unfold thetaKO
  have e : ((negGA _ u, γ * g) : GA D (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) × GA D (G.pT (.chi (i : ℕ) ((j : ℕ) + 1)))) =
      (1, γ) * (negGA _ u, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h1)

end GlobalTheory.BigRouteInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordinateUniqueNeZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := (Spec.map_comp _ _).symm

theorem exists_datum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
    (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) y)
    (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ ksOpen M i k) :
    ∃ (_ : Algebra c.F K) (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K))
      (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
      (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
      (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k (z ≫ toFlag M) hk Q ∧ FrBor t Q P ∧ IsTanFrame (psiSet H) P v ∧
      (∀ b, zv b ≫ toFlag M = X.ptY (v b)) ∧
      (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 ∧
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g) ≠ 0 := by
  have ho : ⊤ ≤ z ⁻¹ᵁ M.off := fun s hs => (hz hs).1
  have hi : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i := fun s hs => (hz hs).2.1
  have hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s hs =>
    (((common₀ X Z).pull M.σ).mem _ k _).1 (hz hs).2.2
  have hfo : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s hs => by
    have := ho hs
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg, hQex⟩ := exists_chartFr (z ≫ toFlag M) hfo
  obtain ⟨Q, hQ⟩ := hQex k hk
  have hzQ : z ≫ toFlag M = X.ptY Q := FlagCover.eq_ptY hQ.lies
  obtain ⟨W, v, hWP, hWv, hv, hinj⟩ := _root_.GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective X K Q (hKS K Q)
  have hW0 : spMap (TrivSqZeroExt.fstHom K K (TIx Dw (psiSet H) → K)).toRingHom ≫ X.ptY W = z ≫ toFlag M := by
    have e : (TrivSqZeroExt.fstHom K K (TIx Dw (psiSet H) → K)).toRingHom =
        (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)).toRingHom := RingHom.ext fun _ => rfl
    rw [hzQ, e]; exact X.ptY_frMap hWP
  obtain ⟨W', hW'1, hW'2, hW'3⟩ := GlobalTheory.T.existsUnique_modification_lift_sqZero_flag M z ho (X.ptY W) hW0
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero M.K i z hi
  have hW'O := hW'3 _ hi
  have hpre : ∀ {R : Type} [CommRing R] (φ : TrivSqZeroExt K (TIx Dw (psiSet H) → K) →+* R),
      ⊤ ≤ (spMap φ ≫ W') ⁻¹ᵁ M.K.bundle.U i := fun φ s _ => hW'O (Set.mem_univ ((spMap φ).base s))
  let zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X) := fun b =>
    spMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))).toRingHom ≫ W'
  have hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ M.K.bundle.U i := fun b => hpre _
  have hent : ∀ a b, (evalPt (zv b) _ (hzv b) (g a)).snd = (evalPt W' _ hW'O (g a)).snd b := fun a b => by
    simp only [zv]
    rw [evalPt_spMap_comp _ W' _ hW'O]
    simp [Pi.single_apply]
  have hdet : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) _ (hzv _) (g a)).snd).det ≠ 0 := by
    intro hd
    obtain ⟨m, hm0, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    let m' : TIx Dw (psiSet H) → K := fun b => m ((tanOrd Dw).symm b)
    obtain ⟨u, hu⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.dir c m') W
    obtain ⟨P₀, hP₀⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.cst c K) Q
    have key := GlobalTheory.T.eq_zero_tangent_of_jacobian_derivs_vanish M.K i z hi g hg (spMap (GlobalTheory.FlagTan.dir c m').toRingHom ≫ W') (hpre _) ?_ ?_ ?_
    · apply hm0
      have hm'0 : m' = 0 := by
        refine hinj m' u P₀ hu hP₀ ?_
        rw [← X.ptY_frMap hu, ← X.ptY_frMap hP₀, ← hW'1, ← hzQ, ← Category.assoc, key, Category.assoc]
        rfl
      funext b
      simpa [m'] using congrFun hm'0 (tanOrd Dw b)
    · rw [← Category.assoc, spectrumMap_comp, ← hW'2]
      congr 2
      ext x <;> simp
    · have a1 : W' ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap (algebraMap c.F _) := by
        rw [← Category.assoc M.σ, ← Category.assoc W']
        exact (congrArg (· ≫ flagStr X) hW'1).trans (ptY_str X W)
      have a2 : z ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap (algebraMap c.F K) := by
        rw [← Category.assoc M.σ, ← Category.assoc z]
        exact (congrArg (· ≫ flagStr X) hzQ).trans (ptY_str X Q)
      change (spMap _ ≫ W') ≫ M.σ ≫ inc₀ X Z ≫ flagStr X = spMap _ ≫ z ≫ M.σ ≫ inc₀ X Z ≫ flagStr X
      rw [Category.assoc, a1, a2, spectrumMap_comp, spectrumMap_comp]
      refine congrArg spMap (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      rfl
    · intro a
      rw [evalPt_spMap_comp _ W' _ hW'O]
      have := congrFun hm a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hent] at this
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir]
      rw [← (tanOrd Dw).sum_comp]
      simpa [m'] using this
  refine ⟨alg, Q, Q, 1, v, zv, _, le_rfl, g, hi, hzv, hk, hQ,
    (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).1 Q, hv, fun b => ?_, hdet, ?_⟩
  · simp only [zv]
    rw [Category.assoc, hW'1]
    exact X.ptY_frMap (hWv b)
  · simpa using hg

theorem ksRel_unique_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y}
    {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)),
    (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) →
    ∀ (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k →
      (∀ x y : K, KSRel M i k z x → KSRel M i k z y → x = y) ∧ ∀ x : K, KSRel M i k z x → x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS i k K _ z hz
  obtain ⟨alg, P, Q, t, v, zv, O, hO, g, hz', hzv, hk, hQ, ht, hv, hl, hd, hr⟩ := exists_datum M hKS i k K z hz
  refine ⟨fun x y hx hy => mul_right_cancel₀ hd ((hx P Q t v zv O hO g hz' hzv hk hQ ht hv hl).trans
    (hy P Q t v zv O hO g hz' hzv hk hQ ht hv hl).symm), fun x hx h0 => hr ?_⟩
  have := hx P Q t v zv O hO g hz' hzv hk hQ ht hv hl
  rw [h0, zero_mul] at this
  exact this.symm

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop

namespace GlobalTheory.DiffSOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_diff_of_split (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have h' : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L := by
    rw [← h, Formalism.L2.SG.Pf.TypedLoc.primesOver_eq L hp]
    exact (Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw).symm
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef K L hp h' v hv
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem not_dvd_differentIdeal : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D large₂ hR v hv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  rcases (S1_mem_OmF D).1 hv with h | h | h | h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 0 h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 1 h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde_prime Pm.pde_split.1 v h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde'_prime Pm.pde_split.2 v h

end GlobalTheory.DiffSOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantSpanSpanEqGeneratorDets
section
open NumberField

namespace GlobalTheory.IdxTensor

theorem dets_span_eq {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  set T : Set F := {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} with hT
  apply le_antisymm
  · unfold dets
    rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    have key : ∀ s : Finset (Fin p), ∀ y : Fin p → Fin p → F,
        (∀ i, y i ∈ Submodule.span (𝓞 F) S) → (∀ i, i ∉ s → y i ∈ S) →
          (Matrix.of y).det ∈ Submodule.span (𝓞 F) T := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y _ h
        exact Submodule.subset_span ⟨y, fun i => h i (Finset.notMem_empty i), rfl⟩
      | insert a s ha ih =>
        intro y hy hs
        have upd : ∀ v, Matrix.of (Function.update y a v) = Matrix.updateRow (Matrix.of y) a v := fun v => rfl
        have hv : ∀ v ∈ Submodule.span (𝓞 F) S,
            (Matrix.updateRow (Matrix.of y) a v).det ∈ Submodule.span (𝓞 F) T := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rw [← upd]
            apply ih
            · intro i
              by_cases h : i = a
              · subst h; simpa using Submodule.subset_span hx
              · simpa [Function.update_of_ne h] using hy i
            · intro i hi
              by_cases h : i = a
              · subst h; simpa using hx
              · simpa [Function.update_of_ne h] using hs i (by simp [h, hi])
          | zero =>
            rw [Matrix.det_eq_zero_of_row_eq_zero a (by intro j; simp)]
            exact Submodule.zero_mem _
          | add x z _ _ hx hz =>
            rw [Matrix.det_updateRow_add]
            exact Submodule.add_mem _ hx hz
          | smul r x _ hx =>
            rw [← algebraMap_smul F r x, Matrix.det_updateRow_smul, ← Algebra.smul_def]
            exact Submodule.smul_mem _ r hx
        have := hv (y a) (hy a)
        rwa [← upd, Function.update_eq_self] at this
    exact key Finset.univ y hy (by simp)
  · unfold dets
    apply Submodule.span_mono
    rintro d ⟨y, hy, rfl⟩
    exact ⟨y, fun i => Submodule.subset_span (hy i), rfl⟩

end GlobalTheory.IdxTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
section
open GlobalTheory.SqTop

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest

namespace GlobalTheory.SqTop

theorem exists_coord_ne_of_norm_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}
    (P : GlobalTheory.NormSum.Pair D cc δ t0 Q) (h : P.norm ≠ 0) : ∃ g T, P.coord g T ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [GlobalTheory.NormSum.Pair.norm, GlobalTheory.NormSum.Pair.sq, hc]

theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  simp only [h0, botBig, botSmall, halfRank]
  omega

end GlobalTheory.SqTop

end
end

