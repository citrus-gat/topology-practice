import topology.basic
import topology.metric_space.basic 


section 
open metric

-- Open balls in an ultrametric space are closed 
example {X : Type*}[metric_space X] (x : X) (r : ℝ) (r_pos : r > 0) (strong_ti : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z)) : 
is_closed (ball x r) := 
begin 
  -- To show B(x, r) is closed, it suffices to show its complement is open 
  suffices : is_open (ball x r)ᶜ, 
      { rwa ← is_open_compl_iff },
  -- That is, for all y ∈ X \ B(x, r), there is an B(y, ε) ⊆ X \ B(x, r)
  suffices : ∀ y ∈ (ball x r)ᶜ, ∃ ε > 0, (ball y ε) ⊆ (ball x r)ᶜ, 
      { rwa is_open_iff }, 
  intros y y_not_in,      -- We let y be arbiturary with y ∈ X \ B(x, r), 
                          -- and we want to show B(y, ε) ⊆ X \ B(x, r)
  use [r, r_pos],         -- We claim that ε = r works. That is, B(y, r) ⊆ X \ B(x, r)
  intros z hz,            -- To show this, we let z ∈ B(y, r), and we wts z ∈ X \ B(x, r),
  change ¬ dist z x < r,  -- that is, to show it is not the case that d(x, z) < r. 
  by_contradiction H,     -- We preceed by contradiction 
                          -- (directly we know that d(x,y) ≤ max{d(x,z), d(y,z)}, 
                          --  and d(x,y) ≥ r, d(y,z) < r, so we must have d(x,z) ≥ r, 
                          --  but to me the above argument is not as easy to write :/ )
  have hc : dist y x < r :=   -- by our new assumption, we can show d(y,x) < r: 
    calc dist y x ≤ max (dist y z) (dist z x) : strong_ti y z x
              ... = max (dist z y) (dist z x) : by rw dist_comm y z
              ... < r                         : max_lt hz H, 
  exact y_not_in hc,      -- And that contradicts with the hypothesis that y ∈ X \ B(x, r)
end

-- Closed balls in an ultrametric space are open
example {X : Type*}[metric_space X] (x : X) (r : ℝ) (r_pos : r > 0) (strong_ti : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z) ): 
is_open (closed_ball x r) := 
begin 
  -- Our goal is to show the closed ball B̅(x, r) is open, 
  -- so it suffices to show that for all y ∈ B̅(x, r), there exists B(y, ε) ⊆ B̅(x, r)
  suffices : ∀ y ∈ (closed_ball x r), ∃ ε > 0, (ball y ε) ⊆ (closed_ball x r), 
      { rwa is_open_iff /- The theorem `is_open_iff` proves the above claim -/ },
  intros y y_in,  -- Let y be arbiturary with the assumption that y ∈ B̅(x, r)
                  -- Then we want to find an ε that satisfies B(y, ε) ⊆ B̅(x, r)
  use [r, r_pos], -- We claim that ε = r works. 
  intros z z_in,  -- To show that, we let z ∈ B(y, ε), 
                  -- and we preceed to show that z ∈ B̅(x, r), that is, d(z, x) ≤ r. 
  calc dist z x ≤ max (dist z y) (dist y x) : strong_ti z y x
            ... ≤ max r r                   : max_le_max (le_of_lt z_in) y_in 
            ... = r                         : max_self r
end 

end -- Ends the section 

-- If X Y are topological spaces, Y is Hausdorff, f and g are continuous functions from X to Y, 
-- then the set {x ∈ X : f x = g x} is closed. 
example {X Y : Type*}[topological_space X][topological_space Y][t2_space Y]{f g : X → Y} :
continuous f → continuous g → is_closed {x : X | f x = g x} := 
begin 
  intros hfcts hgcts,
  suffices : is_open {x : X | f x ≠ g x}, { rwa ← is_open_compl_iff },
  rw is_open_iff_forall_mem_open,
  intros x x_in,
  rcases t2_separation (x_in) with ⟨U, V, U_open, V_open, fx_in_U, gx_in_V, UdisjV⟩,
  use (f ⁻¹' U) ∩ (g ⁻¹' V),
  repeat {split},
  { -- (f ⁻¹' U) ∩ (g ⁻¹' V) is contained in the set {x : X | f x ≠ g x}
    show (f ⁻¹' U) ∩ (g ⁻¹' V) ⊆ {x : X | f x ≠ g x},
    intros x' x'_in, 
    rw set.mem_inter_iff at x'_in,
    repeat {rw set.mem_preimage at x'_in},
    exact disjoint.ne_of_mem UdisjV x'_in.left x'_in.right },
  { -- (f ⁻¹' U) ∩ (g ⁻¹' V) is open
    show is_open ((f ⁻¹' U) ∩ (g ⁻¹' V)),
    exact is_open.inter (is_open.preimage hfcts U_open) (is_open.preimage hgcts V_open) }, 
    -- x ∈ f⁻¹(U) and x ∈ f⁻¹(V)
  repeat { rwa set.mem_preimage },
end



