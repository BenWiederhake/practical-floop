HALFBASE = 8

def split(tail):
    head = 0
    cont = True
    while cont:
        tail, popped = divmod(tail, HALFBASE * 2)
        cont, head_push = divmod(popped, HALFBASE)
        assert 0 <= cont <= 1
        head *= HALFBASE
        head += head_push
    return head, tail


def join(head, tail):
    if head == tail == 0:
        return HALFBASE
    head, topush = divmod(head, HALFBASE)
    tail *= HALFBASE * 2
    tail += topush
    while head > 0:
        head, topush = divmod(head, HALFBASE)
        tail *= HALFBASE * 2
        tail += HALFBASE + topush
    return tail
