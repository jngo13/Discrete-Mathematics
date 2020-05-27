structure Photo : Type :=
photo :: (caption: string) (filename :string) (rating : nat)


--def p1:= Photo.photop
open Photo

--lamda
--pros: gives a lot of insight into what you write, see exactly whats going on
def change_rating: Photo → nat → Photo :=
    λ p n,
        photo p.caption p.filename n

-- a product type is a type where you have multiple fields
-- tuple -> multiple fields (x y : ℕ ) x and y

--c style
def change_rating' (p: Photo) (n: nat) : Photo:=
    photo p.caption p.filename nat

--by case
def change_rating'' : Photo → nat → Photo
| p n := photo p.caption p.filename

def p1:= photo "a caption" "a file/foo.jpg" 
def p2 := change_rating p1 3

#eval p1.caption
#eval p1.filename
#eval p1.rating

#eval p2.caption
#eval p2.filename
#eval p2.rating

