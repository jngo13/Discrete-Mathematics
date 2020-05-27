-- Justin Ngo
-- jmn4fms
-- 2/3/20
-- Sullivan 2102-001

import .dm_box

def b1 := dm_box.mk 5
def b2 := dm_box.mk tt

#reduce unbox b1
#reduce unbox b2

#reduce unbox' b1
#reduce unbox' b2

#reduce unbox' b1
#reduce unbox' b2